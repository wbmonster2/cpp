
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX

#include <windows.h>
#include <d3d11.h>
#include <tchar.h>

#include <shlobj.h>
#include <string>
#include <vector>
#include <sstream>
#include <algorithm>
#include <fstream>
#include <exception>
#include <cstdint>
#include <thread>
#include <atomic>
#include <mutex>
#include <chrono>
#include <random>
#include <cctype>
#include <cmath>
#include <map>
#include <array>

#include "imgui.h"
#include "imgui_impl_win32.h"
#include "imgui_impl_dx11.h"

#include <opencv2/opencv.hpp>

#pragma comment(lib, "shell32.lib")
#pragma comment(lib, "d3d11.lib")
#pragma comment(lib, "dxgi.lib")
#pragma comment(lib, "d3dcompiler.lib")

// ============================================================
// CONFIGURATION
// ============================================================

static const wchar_t* ADB_PATH =
L"C:\\LDPlayer\\LDPlayer9\\adb.exe";

static constexpr double PHOTON_MATCH_THRESHOLD = 0.86;
static constexpr int SCREEN_WIDTH = 960;
static constexpr int SCREEN_HEIGHT = 540;

static constexpr int LOGIN_TIMEOUT_MS = 35000;
static constexpr int AFTER_LOGIN_TIMEOUT_MS = 45000;

// Максимальное ожидание появления каждого последующего шаблона.
static constexpr int STAGE_TIMEOUT_MS = 300000;

// Интервал между проверками изображения.
static constexpr int DETECTION_INTERVAL_MS = 700;

// Пауза перед первым действием.
static constexpr int INITIAL_DELAY_MS = 5000;

// ============================================================
// GLOBAL STATE
// ============================================================

static std::mutex g_NamesFileMutex;
static std::string g_PhotonDetectionLog;
static std::string g_PhotonLaunchLog;

static std::string g_ADBOutput;
static std::string g_ADBStatus = "Not connected";
static std::string g_Notification = "SmartClick initialized";

static int g_CurrentPage = 0;
static int g_SelectedDevice = -1;
static int g_SelectedWindow = -1;

static std::atomic<bool> g_AutomationBusy{ false };
static std::thread g_AutomationThread;
static std::mutex g_LogMutex;

static char g_RegistrationPassword[128] = "SmartClick123";

// ============================================================
// IMAGE TEMPLATES
// ============================================================

static cv::Mat g_PhotonReadyTemplate;
static cv::Mat g_PhotonAfterLoginTemplate;

static std::map<std::string, cv::Mat> g_StageTemplates;

static bool g_TemplatesLoaded = false;
static std::string g_TemplateStatus;

// ============================================================
// DIRECTX
// ============================================================

static ID3D11Device* g_pd3dDevice = nullptr;
static ID3D11DeviceContext* g_pd3dDeviceContext = nullptr;
static IDXGISwapChain* g_pSwapChain = nullptr;
static ID3D11RenderTargetView* g_mainRenderTargetView = nullptr;

static HWND g_hWnd = nullptr;
static bool g_Running = true;

// ============================================================
// DATA
// ============================================================

struct ADBDevice
{
    std::string id;
    std::string status;
    std::string model;
    bool selected = false;
};

struct EmulatorWindow
{
    HWND handle = nullptr;
    std::wstring title;
};

struct AutomationResult
{
    bool success = false;
    bool loginConfirmed = false;
    bool nameEntered = false;
    bool surnameEntered = false;
    bool registrationCompleted = false;
};

static std::vector<ADBDevice> g_Devices;
static std::vector<EmulatorWindow> g_EmulatorWindows;

static const char* g_PageNames[] =
{
    "Dashboard",
    "Macro Recorder",
    "Vision Engine",
    "Emulator Manager",
    "Auto Launch",
    "Settings",
    "Logs"
};

// ============================================================
// STRING HELPERS
// ============================================================

std::string WideToUtf8(const std::wstring& text)
{
    if (text.empty())
        return {};

    int size = WideCharToMultiByte(
        CP_UTF8, 0,
        text.data(),
        static_cast<int>(text.size()),
        nullptr, 0, nullptr, nullptr
    );

    if (size <= 0)
        return {};

    std::string result(static_cast<size_t>(size), '\0');

    WideCharToMultiByte(
        CP_UTF8, 0,
        text.data(),
        static_cast<int>(text.size()),
        result.data(),
        size, nullptr, nullptr
    );

    return result;
}

std::wstring Utf8ToWide(const std::string& text)
{
    if (text.empty())
        return {};

    int size = MultiByteToWideChar(
        CP_UTF8, 0,
        text.data(),
        static_cast<int>(text.size()),
        nullptr, 0
    );

    if (size <= 0)
        return std::wstring(text.begin(), text.end());

    std::wstring result(static_cast<size_t>(size), L'\0');

    MultiByteToWideChar(
        CP_UTF8, 0,
        text.data(),
        static_cast<int>(text.size()),
        result.data(),
        size
    );

    return result;
}

std::string Trim(const std::string& value)
{
    size_t first = value.find_first_not_of(" \t\r\n");

    if (first == std::string::npos)
        return {};

    size_t last = value.find_last_not_of(" \t\r\n");

    return value.substr(first, last - first + 1);
}

std::string GetModelFromLine(const std::string& line)
{
    const std::string key = "model:";
    size_t position = line.find(key);

    if (position == std::string::npos)
        return "Unknown";

    position += key.length();

    size_t end = line.find(' ', position);

    if (end == std::string::npos)
        end = line.length();

    return line.substr(position, end - position);
}

bool ContainsIgnoreCase(
    const std::wstring& text,
    const std::wstring& search)
{
    std::wstring a = text;
    std::wstring b = search;

    std::transform(a.begin(), a.end(), a.begin(), towlower);
    std::transform(b.begin(), b.end(), b.begin(), towlower);

    return a.find(b) != std::wstring::npos;
}

// ============================================================
// PROCESS EXECUTION
// ============================================================

bool RunProcess(
    const std::wstring& executable,
    const std::wstring& arguments,
    std::vector<unsigned char>& output,
    DWORD timeoutMs,
    bool captureStderr = true)
{
    output.clear();

    SECURITY_ATTRIBUTES security{};
    security.nLength = sizeof(SECURITY_ATTRIBUTES);
    security.bInheritHandle = TRUE;

    HANDLE readPipe = nullptr;
    HANDLE writePipe = nullptr;

    if (!CreatePipe(&readPipe, &writePipe, &security, 0))
        return false;

    SetHandleInformation(readPipe, HANDLE_FLAG_INHERIT, 0);

    HANDLE nullHandle = CreateFileW(
        L"NUL",
        GENERIC_WRITE,
        FILE_SHARE_READ | FILE_SHARE_WRITE,
        &security,
        OPEN_EXISTING,
        FILE_ATTRIBUTE_NORMAL,
        nullptr
    );

    STARTUPINFOW startup{};
    startup.cb = sizeof(startup);
    startup.dwFlags = STARTF_USESTDHANDLES;
    startup.hStdOutput = writePipe;
    startup.hStdError = captureStderr ? writePipe : nullHandle;
    startup.hStdInput = GetStdHandle(STD_INPUT_HANDLE);

    PROCESS_INFORMATION process{};

    std::wstring command =
        L"\"" + executable + L"\" " + arguments;

    BOOL created = CreateProcessW(
        executable.c_str(),
        command.data(),
        nullptr,
        nullptr,
        TRUE,
        CREATE_NO_WINDOW,
        nullptr,
        nullptr,
        &startup,
        &process
    );

    CloseHandle(writePipe);

    if (nullHandle != INVALID_HANDLE_VALUE)
        CloseHandle(nullHandle);

    if (!created)
    {
        CloseHandle(readPipe);
        return false;
    }

    ULONGLONG startTime = GetTickCount64();

    bool processFinished = false;
    bool pipeFinished = false;
    bool timedOut = false;

    unsigned char buffer[16384];

    while (!pipeFinished)
    {
        DWORD available = 0;

        BOOL peekResult = PeekNamedPipe(
            readPipe,
            nullptr,
            0,
            nullptr,
            &available,
            nullptr
        );

        if (!peekResult)
        {
            pipeFinished = true;
            break;
        }

        if (available > 0)
        {
            DWORD bytesRead = 0;

            DWORD toRead = std::min<DWORD>(
                available,
                static_cast<DWORD>(sizeof(buffer))
            );

            if (ReadFile(
                readPipe,
                buffer,
                toRead,
                &bytesRead,
                nullptr) && bytesRead > 0)
            {
                output.insert(
                    output.end(),
                    buffer,
                    buffer + bytesRead
                );
            }
        }

        if (WaitForSingleObject(process.hProcess, 0) == WAIT_OBJECT_0)
            processFinished = true;

        if (!processFinished &&
            GetTickCount64() - startTime >= timeoutMs)
        {
            timedOut = true;
            TerminateProcess(process.hProcess, 1);
            WaitForSingleObject(process.hProcess, 2000);
            processFinished = true;
        }

        if (processFinished && available == 0)
        {
            DWORD remaining = 0;

            if (!PeekNamedPipe(
                readPipe,
                nullptr,
                0,
                nullptr,
                &remaining,
                nullptr) || remaining == 0)
            {
                pipeFinished = true;
            }
        }

        if (!processFinished || available == 0)
            Sleep(5);
    }

    CloseHandle(readPipe);

    DWORD exitCode = 1;

    if (!timedOut)
        GetExitCodeProcess(process.hProcess, &exitCode);

    CloseHandle(process.hThread);
    CloseHandle(process.hProcess);

    return !timedOut && exitCode == 0;
}

std::string ExecuteADB(
    const std::wstring& arguments,
    DWORD timeoutMs = 10000)
{
    std::vector<unsigned char> data;

    bool success = RunProcess(
        ADB_PATH,
        arguments,
        data,
        timeoutMs,
        true
    );

    std::string output(data.begin(), data.end());

    if (!success)
    {
        if (output.empty())
            output = "ADB process failed or timed out.";

        return "ERROR: " + output;
    }

    return output;
}

bool IsADBError(const std::string& output)
{
    return output.rfind("ERROR:", 0) == 0;
}

std::wstring DeviceArgument(const std::string& deviceId)
{
    return Utf8ToWide(deviceId);
}

// ============================================================
// ADB INPUT
// ============================================================

bool TapADB(
    const std::string& deviceId,
    int x,
    int y,
    std::string& diagnostic)
{
    if (x < 0 || x >= SCREEN_WIDTH ||
        y < 0 || y >= SCREEN_HEIGHT)
    {
        diagnostic = "Invalid tap coordinates.";
        return false;
    }

    const std::wstring serial = DeviceArgument(deviceId);
    const std::wstring sx = std::to_wstring(x);
    const std::wstring sy = std::to_wstring(y);

    // Explicit touchscreen source is more reliable for LDPlayer's
    // WebView/game UI than the generic input tap source.
    std::wstring command =
        L"-s " + serial +
        L" shell input touchscreen tap " + sx + L" " + sy;

    std::string output = ExecuteADB(command, 8000);

    if (!IsADBError(output))
    {
        diagnostic = "Touchscreen tap sent at (" +
            std::to_string(x) + ", " + std::to_string(y) + ").";
        return true;
    }

    // Fallback gesture: DOWN/MOVE/UP at the same coordinates.
    command =
        L"-s " + serial +
        L" shell input touchscreen swipe " +
        sx + L" " + sy + L" " + sx + L" " + sy + L" 120";

    output = ExecuteADB(command, 8000);

    if (!IsADBError(output))
    {
        diagnostic = "Touchscreen swipe-tap sent at (" +
            std::to_string(x) + ", " + std::to_string(y) + ").";
        return true;
    }

    // Last fallback for LDPlayer images exposing a mouse input source.
    command =
        L"-s " + serial +
        L" shell input mouse tap " + sx + L" " + sy;

    output = ExecuteADB(command, 8000);

    if (IsADBError(output))
    {
        diagnostic = "Touch input failed: " + output;
        return false;
    }

    diagnostic = "Mouse tap sent at (" +
        std::to_string(x) + ", " + std::to_string(y) + ").";
    return true;
}

bool SendBackspaceADB(
    const std::string& deviceId,
    int count,
    std::string& diagnostic)
{
    if (count < 1)
        count = 1;

    std::wstring shellCommand = L"input keyevent 123; input keyevent";

    for (int i = 0; i < count; ++i)
        shellCommand += L" 67";

    std::wstring arguments =
        L"-s " + DeviceArgument(deviceId) +
        L" shell \"" + shellCommand + L"\"";

    std::string output = ExecuteADB(arguments, 10000);

    if (IsADBError(output))
    {
        diagnostic = output;
        return false;
    }

    diagnostic =
        std::to_string(count) +
        " Backspace events sent.";

    return true;
}

bool ClearADBTextField(
    const std::string& deviceId,
    int x,
    int y,
    std::string& diagnostic)
{
    if (!TapADB(deviceId, x, y, diagnostic))
        return false;

    Sleep(150);

    if (!SendBackspaceADB(deviceId, 20, diagnostic))
        return false;

    return true;
}

// Вводим только латинские буквы и цифры.
// Это исключает проблемы с экранированием символов в ADB shell input text.
bool IsSafeADBText(const std::string& value)
{
    if (value.empty())
        return false;

    for (unsigned char c : value)
    {
        if (!std::isalnum(c))
            return false;
    }

    return true;
}

// Detect errors printed by Android's input command even when the adb
// process itself exits with code 0. Checking only the Windows process
// exit code can incorrectly treat "Unknown command" as successful input.
bool IsAndroidInputError(const std::string& output)
{
    std::string lower = output;
    std::transform(
        lower.begin(),
        lower.end(),
        lower.begin(),
        [](unsigned char c) { return static_cast<char>(std::tolower(c)); }
    );

    return lower.find("error:") != std::string::npos ||
        lower.find("unknown command") != std::string::npos ||
        lower.find("usage: input") != std::string::npos ||
        lower.find("input: not found") != std::string::npos;
}

bool InputADBText(
    const std::string& deviceId,
    const std::string& value,
    std::string& diagnostic)
{
    if (!IsSafeADBText(value))
    {
        diagnostic =
            "Text contains unsupported characters. "
            "Use English letters and digits only.";
        return false;
    }

    const std::wstring serial = DeviceArgument(deviceId);
    const std::wstring text = Utf8ToWide(value);

    // Send characters separately instead of one large burst.
    // Some embedded game/WebView fields drop fast consecutive key events.
    std::wstring shellCommand;

    for (wchar_t ch : text)
    {
        if (!shellCommand.empty())
            shellCommand += L"; sleep 0.08; ";

        shellCommand += L"input keyboard text ";
        shellCommand += ch;
    }

    std::wstring arguments =
        L"-s " + serial +
        L" shell \"" + shellCommand + L"\"";

    std::string output = ExecuteADB(
        arguments,
        static_cast<DWORD>(std::max<size_t>(15000, text.size() * 1200))
    );

    if (!IsADBError(output) && !IsAndroidInputError(output))
    {
        diagnostic =
            "Characters sent one by one with 80 ms intervals. "
            "ADB output: " +
            (output.empty() ? std::string("<empty>") : output);
        return true;
    }

    const std::string slowInputError = output;

    // Compatibility fallback: try one standard text command if the
    // emulator does not support one of the shell features above.
    arguments =
        L"-s " + serial +
        L" shell input keyboard text " + text;

    output = ExecuteADB(arguments, 15000);

    if (IsADBError(output) || IsAndroidInputError(output))
    {
        diagnostic =
            "Slow per-character input and bulk input both failed. "
            "Per-character: " + slowInputError +
            " Bulk: " + output;
        return false;
    }

    diagnostic =
        "Text sent using bulk Android keyboard input fallback. "
        "ADB output: " +
        (output.empty() ? std::string("<empty>") : output);
    return true;
}
bool VerifyEnteredNamesADB(
    const std::string& deviceId,
    const std::string& firstName,
    const std::string& lastName,
    std::string& diagnostic)
{
    std::wstring arguments =
        L"-s " + DeviceArgument(deviceId) +
        L" shell \"uiautomator dump "
        L"/sdcard/smartclick_ui.xml "
        L">/dev/null 2>&1 && "
        L"cat /sdcard/smartclick_ui.xml\"";

    std::string output = ExecuteADB(arguments, 20000);

    if (IsADBError(output))
    {
        diagnostic =
            "UI Automator failed: " + output;

        return false;
    }

    if (output.find(firstName) == std::string::npos)
    {
        diagnostic =
            "Verification failed: generated first name "
            "was not found in Android UI.";

        return false;
    }

    if (output.find(lastName) == std::string::npos)
    {
        diagnostic =
            "Verification failed: generated surname "
            "was not found in Android UI.";

        return false;
    }

    diagnostic =
        "VERIFIED: both generated names are present "
        "in Android UI.";

    return true;
}

// ============================================================
// FILE PATHS
// ============================================================

std::wstring GetExecutableDirectory()
{
    wchar_t buffer[MAX_PATH]{};

    DWORD length = GetModuleFileNameW(
        nullptr,
        buffer,
        MAX_PATH
    );

    if (length == 0 || length >= MAX_PATH)
        return L".";

    std::wstring path(buffer, length);

    size_t position = path.find_last_of(L"\\/");

    if (position != std::wstring::npos)
        path.resize(position);

    return path;
}

std::wstring GetTemplatePath(const std::wstring& filename)
{
    return GetExecutableDirectory() + L"\\" + filename;
}

// ============================================================
// GENERATED NAMES FILE
// ============================================================

bool SaveGeneratedName(
    const std::string& deviceId,
    const std::string& firstName,
    const std::string& lastName,
    const std::string& password,
    std::string& diagnostic)
{
    wchar_t desktopPath[MAX_PATH]{};

    HRESULT result = SHGetFolderPathW(
        nullptr,
        CSIDL_DESKTOPDIRECTORY,
        nullptr,
        SHGFP_TYPE_CURRENT,
        desktopPath
    );

    if (FAILED(result))
    {
        diagnostic = "Cannot get Windows Desktop path.";
        return false;
    }

    std::wstring filePath =
        std::wstring(desktopPath) +
        L"\\SmartClick_Names.txt";

    std::string line =
        "login - \"" + firstName + "_" + lastName +
        "\", password - \"" + password + "\"\r\n";

    std::lock_guard<std::mutex> lock(g_NamesFileMutex);

    HANDLE file = CreateFileW(
        filePath.c_str(),
        FILE_APPEND_DATA,
        FILE_SHARE_READ,
        nullptr,
        OPEN_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        nullptr
    );

    if (file == INVALID_HANDLE_VALUE)
    {
        diagnostic = "Cannot create or open SmartClick_Names.txt.";
        return false;
    }

    DWORD bytesWritten = 0;

    BOOL written = WriteFile(
        file,
        line.data(),
        static_cast<DWORD>(line.size()),
        &bytesWritten,
        nullptr
    );

    CloseHandle(file);

    if (!written || bytesWritten != line.size())
    {
        diagnostic = "Cannot write generated name to file.";
        return false;
    }

    diagnostic = "Saved to Desktop: SmartClick_Names.txt";
    return true;
}

// ============================================================
// FILE READING
// ============================================================

bool ReadBinaryFile(
    const std::wstring& path,
    std::vector<unsigned char>& data,
    std::string& diagnostic)
{
    data.clear();

    HANDLE file = CreateFileW(
        path.c_str(),
        GENERIC_READ,
        FILE_SHARE_READ,
        nullptr,
        OPEN_EXISTING,
        FILE_ATTRIBUTE_NORMAL,
        nullptr
    );

    if (file == INVALID_HANDLE_VALUE)
    {
        diagnostic =
            "Cannot open file: " +
            WideToUtf8(path);

        return false;
    }

    LARGE_INTEGER fileSize{};

    if (!GetFileSizeEx(file, &fileSize) ||
        fileSize.QuadPart <= 0 ||
        fileSize.QuadPart > 100 * 1024 * 1024)
    {
        diagnostic = "Invalid template file size.";
        CloseHandle(file);
        return false;
    }

    data.resize(static_cast<size_t>(fileSize.QuadPart));

    size_t totalRead = 0;

    while (totalRead < data.size())
    {
        DWORD requested = static_cast<DWORD>(
            std::min<size_t>(
                data.size() - totalRead,
                1024 * 1024
            )
            );

        DWORD bytesRead = 0;

        if (!ReadFile(
            file,
            data.data() + totalRead,
            requested,
            &bytesRead,
            nullptr) || bytesRead == 0)
        {
            diagnostic = "Cannot read complete file.";
            data.clear();
            CloseHandle(file);
            return false;
        }

        totalRead += bytesRead;
    }

    CloseHandle(file);
    return true;
}

// ============================================================
// TEMPLATE LOADING
// ============================================================

bool LoadPhotonTemplate(
    const std::wstring& path,
    cv::Mat& destination,
    std::string& diagnostic)
{
    std::vector<unsigned char> data;

    if (!ReadBinaryFile(path, data, diagnostic))
        return false;

    try
    {
        cv::Mat decoded = cv::imdecode(
            data,
            cv::IMREAD_COLOR
        );

        if (decoded.empty())
        {
            diagnostic =
                "Cannot decode template: " +
                WideToUtf8(path);

            return false;
        }

        if (decoded.cols > SCREEN_WIDTH ||
            decoded.rows > SCREEN_HEIGHT)
        {
            diagnostic =
                "Template larger than 960x540: " +
                std::to_string(decoded.cols) + "x" +
                std::to_string(decoded.rows);

            return false;
        }

        destination = decoded.clone();

        diagnostic =
            "Loaded " + WideToUtf8(path) +
            " (" +
            std::to_string(decoded.cols) + "x" +
            std::to_string(decoded.rows) + ")";

        return true;
    }
    catch (const cv::Exception& e)
    {
        diagnostic = e.what();
        return false;
    }
}

bool LoadPhotonTemplates()
{
    std::ostringstream status;

    std::string diagnostic;

    bool ready = LoadPhotonTemplate(
        GetTemplatePath(L"photon_ready.png"),
        g_PhotonReadyTemplate,
        diagnostic
    );

    status << "photon_ready.png: " << diagnostic << "\n";

    diagnostic.clear();

    bool after = LoadPhotonTemplate(
        GetTemplatePath(L"photon_after_login.png"),
        g_PhotonAfterLoginTemplate,
        diagnostic
    );

    status << "photon_after_login.png: " << diagnostic << "\n";

    const std::array<std::string, 9> names =
    {
        "play",
        "password",
        "password_repeat",
        "register",
        "skip",
        "next",
        "start",
        "enter_name",
        "enter_lastname"
    };

    g_StageTemplates.clear();

    bool allStageTemplates = true;

    for (const std::string& name : names)
    {
        cv::Mat image;
        std::string fileDiagnostic;

        std::wstring filename =
            Utf8ToWide(name + ".png");

        bool loaded = LoadPhotonTemplate(
            GetTemplatePath(filename),
            image,
            fileDiagnostic
        );

        status
            << name << ".png: "
            << fileDiagnostic << "\n";

        if (loaded)
            g_StageTemplates[name] = image;
        else
            allStageTemplates = false;
    }

    g_TemplatesLoaded = ready && after;

    status
        << "\nLOGIN TEMPLATES: "
        << (g_TemplatesLoaded ? "READY" : "MISSING");

    status
        << "\nREGISTRATION TEMPLATES: "
        << (allStageTemplates ? "READY" : "MISSING");

    g_TemplateStatus = status.str();

    return g_TemplatesLoaded;
}

bool AreAllStageTemplatesLoaded()
{
    const std::array<std::string, 9> names =
    {
        "play",
        "password",
        "password_repeat",
        "register",
        "skip",
        "next",
        "start",
        "enter_name",
        "enter_lastname"
    };

    for (const std::string& name : names)
    {
        auto it = g_StageTemplates.find(name);

        if (it == g_StageTemplates.end() || it->second.empty())
            return false;
    }

    return true;
}

// ============================================================
// SCREENSHOT CAPTURE
// ============================================================

bool CaptureADBScreenshot(
    const std::string& deviceId,
    std::vector<unsigned char>& imageData)
{
    std::wstring arguments =
        L"-s " + DeviceArgument(deviceId) +
        L" exec-out screencap -p";

    return RunProcess(
        ADB_PATH,
        arguments,
        imageData,
        12000,
        false
    );
}

bool DecodeImage(
    const std::vector<unsigned char>& data,
    cv::Mat& image,
    std::string& diagnostic)
{
    image.release();

    if (data.empty())
    {
        diagnostic = "Screenshot data is empty.";
        return false;
    }

    try
    {
        image = cv::imdecode(data, cv::IMREAD_COLOR);

        if (image.empty())
        {
            diagnostic = "Cannot decode screenshot.";
            return false;
        }

        if (image.cols != SCREEN_WIDTH ||
            image.rows != SCREEN_HEIGHT)
        {
            diagnostic =
                "Unexpected screenshot resolution: " +
                std::to_string(image.cols) + "x" +
                std::to_string(image.rows);

            return false;
        }

        return true;
    }
    catch (const cv::Exception& e)
    {
        diagnostic = e.what();
        return false;
    }
}

// ============================================================
// IMAGE RECOGNITION
// ============================================================

bool DetectPhotonTemplate(
    const std::string& deviceId,
    const cv::Mat& templateImage,
    double& confidence,
    POINT& matchCenter,
    std::string& diagnostic)
{
    confidence = 0.0;
    matchCenter = { 0, 0 };
    diagnostic.clear();

    if (templateImage.empty())
    {
        diagnostic = "Template is not loaded.";
        return false;
    }

    try
    {
        std::vector<unsigned char> screenshotData;

        if (!CaptureADBScreenshot(deviceId, screenshotData))
        {
            diagnostic = "Screenshot capture failed.";
            return false;
        }

        cv::Mat screenshot;

        if (!DecodeImage(
            screenshotData,
            screenshot,
            diagnostic))
        {
            return false;
        }

        if (templateImage.cols > screenshot.cols ||
            templateImage.rows > screenshot.rows)
        {
            diagnostic = "Template is larger than screenshot.";
            return false;
        }

        cv::Mat result;

        cv::matchTemplate(
            screenshot,
            templateImage,
            result,
            cv::TM_CCOEFF_NORMED
        );

        double minValue = 0.0;
        double maxValue = 0.0;

        cv::Point minLocation;
        cv::Point maxLocation;

        cv::minMaxLoc(
            result,
            &minValue,
            &maxValue,
            &minLocation,
            &maxLocation
        );

        if (!std::isfinite(maxValue))
        {
            diagnostic = "Invalid matching result.";
            return false;
        }

        confidence = maxValue;

        matchCenter.x =
            maxLocation.x + templateImage.cols / 2;

        matchCenter.y =
            maxLocation.y + templateImage.rows / 2;

        diagnostic =
            "Match: " +
            std::to_string(confidence * 100.0) +
            "%. Center: (" +
            std::to_string(matchCenter.x) + ", " +
            std::to_string(matchCenter.y) + ").";

        return confidence >= PHOTON_MATCH_THRESHOLD;
    }
    catch (const cv::Exception& e)
    {
        diagnostic = e.what();
        return false;
    }
    catch (const std::exception& e)
    {
        diagnostic = e.what();
        return false;
    }
}

bool DetectPhotonReady(
    const std::string& deviceId,
    double& confidence,
    POINT& center,
    std::string& diagnostic)
{
    return DetectPhotonTemplate(
        deviceId,
        g_PhotonReadyTemplate,
        confidence,
        center,
        diagnostic
    );
}

bool DetectPhotonAfterLogin(
    const std::string& deviceId,
    double& confidence,
    std::string& diagnostic)
{
    POINT center{};

    return DetectPhotonTemplate(
        deviceId,
        g_PhotonAfterLoginTemplate,
        confidence,
        center,
        diagnostic
    );
}

bool DetectStage(
    const std::string& deviceId,
    const std::string& templateName,
    double& confidence,
    POINT& center,
    std::string& diagnostic)
{
    auto it = g_StageTemplates.find(templateName);

    if (it == g_StageTemplates.end())
    {
        diagnostic =
            "Template not loaded: " + templateName;

        return false;
    }

    return DetectPhotonTemplate(
        deviceId,
        it->second,
        confidence,
        center,
        diagnostic
    );
}

// Field placeholders can vary slightly due to WebView rendering.
// Match in grayscale at several nearby scales and use a dedicated threshold.
bool DetectInputField(
    const std::string& deviceId,
    const std::string& templateName,
    double& confidence,
    POINT& center,
    std::string& diagnostic)
{
    confidence = 0.0;
    center = { 0, 0 };

    auto it = g_StageTemplates.find(templateName);
    if (it == g_StageTemplates.end() || it->second.empty())
    {
        diagnostic = "Input-field template missing: " + templateName + ".png";
        return false;
    }

    std::vector<unsigned char> screenshotData;
    if (!CaptureADBScreenshot(deviceId, screenshotData))
    {
        diagnostic = "Screenshot capture failed while searching for " + templateName + ".png";
        return false;
    }

    cv::Mat screenshot;
    if (!DecodeImage(screenshotData, screenshot, diagnostic))
        return false;

    try
    {
        cv::Mat screenGray;
        cv::cvtColor(screenshot, screenGray, cv::COLOR_BGR2GRAY);

        cv::Mat templateGray;
        cv::cvtColor(it->second, templateGray, cv::COLOR_BGR2GRAY);

        const double scales[] = { 0.85, 0.90, 0.95, 1.0, 1.05, 1.10, 1.15 };
        cv::Point bestLocation;
        cv::Size bestSize;
        double bestScore = -1.0;

        for (double scale : scales)
        {
            const int width = static_cast<int>(std::round(templateGray.cols * scale));
            const int height = static_cast<int>(std::round(templateGray.rows * scale));

            if (width < 8 || height < 8 ||
                width > screenGray.cols || height > screenGray.rows)
                continue;

            cv::Mat scaledTemplate;
            cv::resize(
                templateGray,
                scaledTemplate,
                cv::Size(width, height),
                0.0,
                0.0,
                scale < 1.0 ? cv::INTER_AREA : cv::INTER_CUBIC
            );

            cv::Mat matchResult;
            cv::matchTemplate(
                screenGray,
                scaledTemplate,
                matchResult,
                cv::TM_CCOEFF_NORMED
            );

            double minValue = 0.0;
            double maxValue = 0.0;
            cv::Point minLocation;
            cv::Point maxLocation;

            cv::minMaxLoc(
                matchResult,
                &minValue,
                &maxValue,
                &minLocation,
                &maxLocation
            );

            if (std::isfinite(maxValue) && maxValue > bestScore)
            {
                bestScore = maxValue;
                bestLocation = maxLocation;
                bestSize = cv::Size(width, height);
            }
        }

        if (bestScore < 0.0)
        {
            diagnostic = "Could not compare input-field template.";
            return false;
        }

        confidence = bestScore;
        center.x = bestLocation.x + bestSize.width / 2;
        center.y = bestLocation.y + bestSize.height / 2;

        diagnostic =
            templateName + ".png field match: " +
            std::to_string(confidence * 100.0) +
            "% at (" + std::to_string(center.x) +
            ", " + std::to_string(center.y) + ").";

        return confidence >= 0.76;
    }
    catch (const cv::Exception& e)
    {
        diagnostic = std::string("OpenCV field matching error: ") + e.what();
        return false;
    }
}

bool WaitForInputField(
    const std::string& deviceId,
    const std::string& templateName,
    POINT& center,
    std::string& diagnostic,
    int timeoutMs = 45000)
{
    const ULONGLONG started = GetTickCount64();
    int consecutiveMatches = 0;
    double confidence = 0.0;
    std::string lastDiagnostic;

    while (GetTickCount64() - started < static_cast<ULONGLONG>(timeoutMs))
    {
        POINT currentCenter{};
        std::string currentDiagnostic;

        if (DetectInputField(
            deviceId,
            templateName,
            confidence,
            currentCenter,
            currentDiagnostic))
        {
            consecutiveMatches++;
            center = currentCenter;

            if (consecutiveMatches >= 2)
            {
                diagnostic = "INPUT FIELD CONFIRMED. " + currentDiagnostic;
                return true;
            }
        }
        else
        {
            consecutiveMatches = 0;
        }

        lastDiagnostic = currentDiagnostic;
        Sleep(450);
    }

    diagnostic =
        "TIMEOUT waiting for " + templateName +
        ".png. Last result: " + lastDiagnostic;
    return false;
}

// ============================================================
// WAIT FOR IMAGE
// ============================================================

bool WaitForPhotonReady(
    const std::string& deviceId,
    double& confidence,
    POINT& center,
    std::string& diagnostic,
    int timeoutMs = LOGIN_TIMEOUT_MS)
{
    ULONGLONG start = GetTickCount64();

    int attempts = 0;
    int consecutive = 0;

    std::string lastDiagnostic;

    while (GetTickCount64() - start <
        static_cast<ULONGLONG>(timeoutMs))
    {
        attempts++;

        POINT currentCenter{};
        std::string currentDiagnostic;

        bool found = DetectPhotonReady(
            deviceId,
            confidence,
            currentCenter,
            currentDiagnostic
        );

        lastDiagnostic = currentDiagnostic;

        if (found)
        {
            consecutive++;
            center = currentCenter;

            if (consecutive >= 2)
            {
                diagnostic =
                    "LOGIN SCREEN CONFIRMED. " +
                    lastDiagnostic;

                return true;
            }
        }
        else
        {
            consecutive = 0;
        }

        Sleep(450);
    }

    diagnostic =
        "LOGIN SCREEN TIMEOUT. Last result: " +
        lastDiagnostic;

    return false;
}

bool WaitForPhotonAfterLogin(
    const std::string& deviceId,
    double& confidence,
    std::string& diagnostic,
    int timeoutMs = AFTER_LOGIN_TIMEOUT_MS)
{
    ULONGLONG start = GetTickCount64();

    int consecutive = 0;
    std::string lastDiagnostic;

    while (GetTickCount64() - start <
        static_cast<ULONGLONG>(timeoutMs))
    {
        std::string currentDiagnostic;

        bool found = DetectPhotonAfterLogin(
            deviceId,
            confidence,
            currentDiagnostic
        );

        lastDiagnostic = currentDiagnostic;

        if (found)
        {
            consecutive++;

            if (consecutive >= 2)
            {
                diagnostic =
                    "AFTER LOGIN SCREEN CONFIRMED. " +
                    lastDiagnostic;

                return true;
            }
        }
        else
        {
            consecutive = 0;
        }

        Sleep(500);
    }

    diagnostic =
        "AFTER LOGIN SCREEN TIMEOUT. " +
        lastDiagnostic;

    return false;
}

// Ждёт появления конкретного шаблона.
// Нужны два последовательных успешных совпадения,
// чтобы не реагировать на случайный кадр.
bool WaitForStage(
    const std::string& deviceId,
    const std::string& templateName,
    POINT& center,
    std::string& diagnostic,
    int timeoutMs = STAGE_TIMEOUT_MS)
{
    ULONGLONG start = GetTickCount64();

    int attempts = 0;
    int consecutive = 0;

    double confidence = 0.0;
    std::string lastDiagnostic;

    while (GetTickCount64() - start <
        static_cast<ULONGLONG>(timeoutMs))
    {
        attempts++;

        POINT currentCenter{};
        std::string currentDiagnostic;

        bool found = DetectStage(
            deviceId,
            templateName,
            confidence,
            currentCenter,
            currentDiagnostic
        );

        lastDiagnostic = currentDiagnostic;

        if (found)
        {
            consecutive++;
            center = currentCenter;

            if (consecutive >= 2)
            {
                diagnostic =
                    templateName +
                    ".png detected. " +
                    lastDiagnostic;

                return true;
            }
        }
        else
        {
            consecutive = 0;
        }

        Sleep(DETECTION_INTERVAL_MS);
    }

    diagnostic =
        "TIMEOUT waiting for " +
        templateName +
        ".png after " +
        std::to_string(timeoutMs / 1000) +
        " seconds. Last result: " +
        lastDiagnostic;

    return false;
}

bool WaitAndTapStage(
    const std::string& deviceId,
    const std::string& templateName,
    std::ostringstream& log)
{
    log << "\nWAITING FOR " << templateName << ".png\n";

    POINT center{};
    std::string diagnostic;

    if (!WaitForStage(
        deviceId,
        templateName,
        center,
        diagnostic))
    {
        log << "FAILED: " << diagnostic << "\n";
        return false;
    }

    log << diagnostic << "\n";

    log
        << "CLICKING "
        << templateName
        << " AT "
        << center.x << ", "
        << center.y << "\n";

    std::string tapDiagnostic;

    if (!TapADB(
        deviceId,
        center.x,
        center.y,
        tapDiagnostic))
    {
        log << "TAP ERROR: " << tapDiagnostic << "\n";
        return false;
    }

    log << tapDiagnostic << "\n";

    return true;
}

// ============================================================
// RANDOM ROLEPLAY NAMES
// ============================================================

std::pair<std::string, std::string> GenerateRoleplayName(
    const std::string& deviceId)
{
    static const std::vector<std::string> firstNames =
    {
        "Aleksandr",
        "Dmitriy",
        "Mikhail",
        "Sergey",
        "Nikolay",
        "Vladimir",
        "Andrey",
        "Artem",
        "Maksim",
        "Ivan",
        "Pavel",
        "Kirill",
        "Roman",
        "Denis",
        "Egor",
        "Viktor",
        "Aleksey",
        "Konstantin",
        "Yaroslav",
        "Timur",
        "Ilya",
        "Oleg",
        "Grigoriy",
        "Stanislav",
        "Vyacheslav",
        "Boris",
        "Fedor",
        "Matvey",
        "Gleb",
        "Nikita"
    };

    static const std::vector<std::string> lastNames =
    {
        "Volkov",
        "Sokolov",
        "Morozov",
        "Lebedev",
        "Novikov",
        "Kuznetsov",
        "Popov",
        "Smirnov",
        "Orlov",
        "Fedorov",
        "Mikhailov",
        "Pavlov",
        "Vinogradov",
        "Belov",
        "Tarasov",
        "Karpov",
        "Zaitsev",
        "Gromov",
        "Baranov",
        "Romanov",
        "Kozlov",
        "Vasiliev",
        "Petrov",
        "Semenov",
        "Nikolaev",
        "Antonov",
        "Sidorov",
        "Medvedev",
        "Zakharov",
        "Mironov"
    };

    std::seed_seq seed
    {
        static_cast<unsigned int>(GetTickCount()),
        static_cast<unsigned int>(
            std::hash<std::string>{}(deviceId)),
        static_cast<unsigned int>(
            std::chrono::high_resolution_clock::now()
                .time_since_epoch().count())
    };

    std::mt19937 generator(seed);

    std::uniform_int_distribution<size_t> firstDistribution(
        0, firstNames.size() - 1
    );

    std::uniform_int_distribution<size_t> lastDistribution(
        0, lastNames.size() - 1
    );

    return
    {
        firstNames[firstDistribution(generator)],
        lastNames[lastDistribution(generator)]
    };
}

// ============================================================
// DEVICE AUTOMATION
// ============================================================

AutomationResult RunPhotonAutomation(
    const ADBDevice& device,
    std::ostringstream& log,
    const std::string& password)
{
    AutomationResult result;

    log << "\n========================================\n";
    log << "DEVICE: " << device.id << "\n";
    log << "========================================\n";

    if (device.status != "device")
    {
        log << "ERROR: ADB device is not ready.\n";
        return result;
    }

    if (!g_TemplatesLoaded)
    {
        log << "ERROR: Login templates are missing.\n";
        return result;
    }

    if (!AreAllStageTemplatesLoaded())
    {
        log << "ERROR: Registration templates are missing.\n";
        log << g_TemplateStatus << "\n";
        return result;
    }

    if (!IsSafeADBText(password))
    {
        log
            << "ERROR: Password must contain only English "
            << "letters and digits.\n";

        return result;
    }

    // --------------------------------------------------------
    // INITIAL DELAY
    // --------------------------------------------------------

    log << "\nINITIAL DELAY: 5 SECONDS\n";

    Sleep(INITIAL_DELAY_MS);

    // --------------------------------------------------------
    // STEP 1: WAIT FOR LOGIN
    // --------------------------------------------------------

    log << "\n[1] WAITING FOR LOGIN BUTTON\n";

    double confidence = 0.0;
    POINT loginCenter{};
    std::string diagnostic;

    if (!WaitForPhotonReady(
        device.id,
        confidence,
        loginCenter,
        diagnostic,
        LOGIN_TIMEOUT_MS))
    {
        log << "FAILED: " << diagnostic << "\n";
        return result;
    }

    log << diagnostic << "\n";

    // --------------------------------------------------------
    // STEP 2: CLICK LOGIN
    // --------------------------------------------------------

    log << "\n[2] CLICK LOGIN\n";

    // Refresh the coordinates immediately before clicking.
    double freshLoginConfidence = 0.0;
    POINT freshLoginCenter{};
    std::string freshLoginDiagnostic;

    if (!DetectPhotonReady(
        device.id,
        freshLoginConfidence,
        freshLoginCenter,
        freshLoginDiagnostic))
    {
        log << "LOGIN BUTTON RECHECK FAILED: "
            << freshLoginDiagnostic << "\n";
        return result;
    }

    loginCenter = freshLoginCenter;
    log << "Fresh login match: "
        << freshLoginDiagnostic << "\n";

    bool afterDetected = false;

    for (int attempt = 1; attempt <= 2; ++attempt)
    {
        log
            << "Login attempt "
            << attempt << "/2 using touchscreen input\n";

        std::string tapDiagnostic;

        if (!TapADB(
            device.id,
            loginCenter.x,
            loginCenter.y,
            tapDiagnostic))
        {
            log << "ERROR: " << tapDiagnostic << "\n";
            return result;
        }

        log << tapDiagnostic << "\n";

        double afterConfidence = 0.0;
        std::string afterDiagnostic;

        afterDetected = WaitForPhotonAfterLogin(
            device.id,
            afterConfidence,
            afterDiagnostic,
            AFTER_LOGIN_TIMEOUT_MS
        );

        log << afterDiagnostic << "\n";

        if (afterDetected)
        {
            result.loginConfirmed = true;
            break;
        }

        if (attempt == 1)
        {
            double retryConfidence = 0.0;
            POINT retryCenter{};
            std::string retryDiagnostic;

            bool stillVisible = DetectPhotonReady(
                device.id,
                retryConfidence,
                retryCenter,
                retryDiagnostic
            );

            log << retryDiagnostic << "\n";

            if (stillVisible)
            {
                loginCenter = retryCenter;
                Sleep(700);
            }
            else
            {
                break;
            }
        }
    }

    if (!result.loginConfirmed)
    {
        log << "FAILED: Login transition not confirmed.\n";
        return result;
    }

    // --------------------------------------------------------
// STEP 3: CLEAR NAME AND IMMEDIATELY INPUT NEW NAME
// --------------------------------------------------------

    log << "\n[3] FIND FIRST-NAME FIELD FROM enter_name.png\n";

    std::string nameDiagnostic;
    POINT firstNameCenter{};

    if (!WaitForInputField(
        device.id,
        "enter_name",
        firstNameCenter,
        nameDiagnostic,
        60000))
    {
        log << "FIRST NAME FIELD NOT FOUND: " << nameDiagnostic << "\n";
        return result;
    }

    log << nameDiagnostic << "\n";

    auto generatedName = GenerateRoleplayName(device.id);
    const std::string firstName = generatedName.first;
    const std::string lastName = generatedName.second;

    log << "\nGENERATED FIRST NAME: " << firstName << "\n";
    log << "CLICKING FIRST-NAME FIELD AT ("
        << firstNameCenter.x << ", " << firstNameCenter.y << ")\n";

    if (!ClearADBTextField(
        device.id,
        firstNameCenter.x,
        firstNameCenter.y,
        nameDiagnostic))
    {
        log << "FIRST NAME FIELD CLEAR ERROR: " << nameDiagnostic << "\n";
        return result;
    }

    log << "FIRST NAME FIELD: " << nameDiagnostic << "\n";
    Sleep(250);

    std::string inputDiagnostic;
    if (!InputADBText(device.id, firstName, inputDiagnostic))
    {
        log << "FIRST NAME INPUT ERROR: " << inputDiagnostic << "\n";
        return result;
    }

    log << "FIRST NAME INPUT: " << inputDiagnostic << "\n";
    Sleep(700);

    // --------------------------------------------------------
    // STEP 4: FIND, CLEAR AND FILL SURNAME FIELD
    // --------------------------------------------------------

    log << "\n[4] FIND LAST-NAME FIELD FROM enter_lastname.png\n";

    std::string surnameDiagnostic;
    POINT lastNameCenter{};

    if (!WaitForInputField(
        device.id,
        "enter_lastname",
        lastNameCenter,
        surnameDiagnostic,
        60000))
    {
        log << "LAST NAME FIELD NOT FOUND: " << surnameDiagnostic << "\n";
        return result;
    }

    log << surnameDiagnostic << "\n";
    log << "CLICKING LAST-NAME FIELD AT ("
        << lastNameCenter.x << ", " << lastNameCenter.y << ")\n";

    if (!ClearADBTextField(
        device.id,
        lastNameCenter.x,
        lastNameCenter.y,
        surnameDiagnostic))
    {
        log << "LAST NAME FIELD CLEAR ERROR: " << surnameDiagnostic << "\n";
        return result;
    }

    log << "LAST NAME FIELD: " << surnameDiagnostic << "\n";
    Sleep(250);

    log << "\nGENERATED LAST NAME: " << lastName << "\n";
    log << "CREDENTIALS: login - \"" << firstName << "_"
        << lastName << "\", password - \"" << password << "\"\n";

    if (!InputADBText(device.id, lastName, inputDiagnostic))
    {
        log << "LAST NAME INPUT ERROR: " << inputDiagnostic << "\n";
        return result;
    }

    log << "LAST NAME INPUT: " << inputDiagnostic << "\n";
    Sleep(700);

    // --------------------------------------------------------
    // STEP 5: CONFIRM INPUT COMMANDS
    // --------------------------------------------------------

    log << "\n[5] NAME AND SURNAME INPUT COMMANDS SENT\n";

    // UIAutomator may not expose WebView/custom fields.
    // Successful ADB input commands are therefore not blocked
    // by an unreliable UIAutomator text dump.
    result.nameEntered = true;
    result.surnameEntered = true;

    // --------------------------------------------------------
    // STEP 6: SAVE GENERATED NAME TO DESKTOP
    // --------------------------------------------------------

    log << "\n[6] SAVE GENERATED NAME\n";

    std::string saveDiagnostic;

    if (!SaveGeneratedName(
        device.id,
        firstName,
        lastName,
        password,
        saveDiagnostic))
    {
        log << "WARNING: " << saveDiagnostic << "\n";
    }
    else
    {
        log << saveDiagnostic << "\n";
    }

    // --------------------------------------------------------
    // STEP 7: WAIT FOR PASSWORD FIELD
    // --------------------------------------------------------

    log << "\n[7] WAIT FOR PASSWORD FIELD\n";

    POINT passwordCenter{};
    std::string passwordDiagnostic;

    if (!WaitForStage(
        device.id,
        "password",
        passwordCenter,
        passwordDiagnostic))
    {
        log << "FAILED: " << passwordDiagnostic << "\n";
        return result;
    }

    log << passwordDiagnostic << "\n";

    if (!TapADB(
        device.id,
        passwordCenter.x,
        passwordCenter.y,
        inputDiagnostic))
    {
        log << "PASSWORD FIELD TAP ERROR: "
            << inputDiagnostic << "\n";
        return result;
    }

    Sleep(200);

    if (!InputADBText(
        device.id,
        password,
        inputDiagnostic))
    {
        log << "PASSWORD INPUT ERROR: "
            << inputDiagnostic << "\n";
        return result;
    }

    log << "Password input command sent.\n";

    // --------------------------------------------------------
    // STEP 8: WAIT FOR PASSWORD REPEAT FIELD
    // --------------------------------------------------------

    log << "\n[8] WAIT FOR PASSWORD REPEAT FIELD\n";

    POINT repeatCenter{};
    std::string repeatDiagnostic;

    if (!WaitForStage(
        device.id,
        "password_repeat",
        repeatCenter,
        repeatDiagnostic))
    {
        log << "FAILED: " << repeatDiagnostic << "\n";
        return result;
    }

    log << repeatDiagnostic << "\n";

    if (!TapADB(
        device.id,
        repeatCenter.x,
        repeatCenter.y,
        inputDiagnostic))
    {
        log << "REPEAT FIELD TAP ERROR: "
            << inputDiagnostic << "\n";
        return result;
    }

    Sleep(200);

    if (!InputADBText(
        device.id,
        password,
        inputDiagnostic))
    {
        log << "REPEAT PASSWORD INPUT ERROR: "
            << inputDiagnostic << "\n";
        return result;
    }

    log << "Repeated password input command sent.\n";

    // --------------------------------------------------------
    // STEP 9: REGISTER
    // --------------------------------------------------------

    log << "\n[9] WAIT FOR REGISTER BUTTON\n";

    if (!WaitAndTapStage(device.id, "register", log))
        return result;

    result.registrationCompleted = true;

    // --------------------------------------------------------
    // STEP 10: SKIP
    // --------------------------------------------------------

    log << "\n[10] WAIT FOR SKIP BUTTON\n";

    if (!WaitAndTapStage(device.id, "skip", log))
        return result;

    // --------------------------------------------------------
    // STEP 11: NEXT
    // --------------------------------------------------------

    log << "\n[11] WAIT FOR NEXT BUTTON\n";

    if (!WaitAndTapStage(device.id, "next", log))
        return result;

    // --------------------------------------------------------
    // STEP 12: START
    // --------------------------------------------------------

    log << "\n[12] WAIT FOR START BUTTON\n";

    if (!WaitAndTapStage(device.id, "start", log))
        return result;

    // --------------------------------------------------------
    // COMPLETE
    // --------------------------------------------------------

    result.success = true;

    log << "\n========================================\n";
    log << "AUTOMATION COMPLETED SUCCESSFULLY.\n";
    log << "Generated name: " << firstName
        << " " << lastName << "\n";
    log << "========================================\n";

    return result;
}

// ============================================================
// AUTOMATION: ALL SELECTED DEVICES
// ============================================================

void StartPhotonAutomation()
{
    if (g_AutomationBusy.load())
        return;

    if (!g_TemplatesLoaded)
    {
        g_Notification = "Login templates are missing.";
        return;
    }

    if (!AreAllStageTemplatesLoaded())
    {
        g_Notification =
            "Some registration PNG templates are missing.";
        return;
    }

    if (!IsSafeADBText(g_RegistrationPassword))
    {
        g_Notification =
            "Password must use English letters and digits only.";
        return;
    }

    std::vector<ADBDevice> selectedDevices;

    for (const ADBDevice& device : g_Devices)
    {
        if (device.selected)
            selectedDevices.push_back(device);
    }

    if (selectedDevices.empty())
    {
        g_Notification = "Select at least one ADB device.";
        return;
    }

    if (g_AutomationThread.joinable())
        g_AutomationThread.join();

    {
        std::lock_guard<std::mutex> lock(g_LogMutex);
        g_PhotonDetectionLog =
            "Starting PHOTON automation...\n";
    }

    g_AutomationBusy = true;
    g_Notification = "PHOTON automation is running...";

    // Snapshot password on the UI thread before starting workers.
    const std::string passwordSnapshot = g_RegistrationPassword;

    g_AutomationThread = std::thread(
        [selectedDevices, passwordSnapshot]()
        {
            std::vector<std::string> deviceLogs(
                selectedDevices.size()
            );

            std::vector<AutomationResult> results(
                selectedDevices.size()
            );

            std::vector<std::thread> workers;

            for (size_t i = 0; i < selectedDevices.size(); ++i)
            {
                workers.emplace_back(
                    [&, i]()
                    {
                        std::ostringstream log;

                        try
                        {
                            results[i] = RunPhotonAutomation(
                                selectedDevices[i],
                                log,
                                passwordSnapshot
                            );
                        }
                        catch (const cv::Exception& e)
                        {
                            log << "OpenCV exception: "
                                << e.what() << "\n";
                        }
                        catch (const std::exception& e)
                        {
                            log << "C++ exception: "
                                << e.what() << "\n";
                        }
                        catch (...)
                        {
                            log << "Unknown automation exception.\n";
                        }

                        deviceLogs[i] = log.str();
                    }
                );
            }

            for (std::thread& worker : workers)
            {
                if (worker.joinable())
                    worker.join();
            }

            int successCount = 0;
            int failedCount = 0;

            std::ostringstream finalLog;

            finalLog << "PHOTON AUTOMATION RESULTS\n";
            finalLog << "Selected devices: "
                << selectedDevices.size() << "\n";

            for (size_t i = 0; i < selectedDevices.size(); ++i)
            {
                finalLog << deviceLogs[i];

                if (results[i].success)
                    successCount++;
                else
                    failedCount++;
            }

            finalLog << "\n========================================\n";
            finalLog << "SUCCESS: " << successCount << "\n";
            finalLog << "FAILED: " << failedCount << "\n";
            finalLog << "========================================\n";

            {
                std::lock_guard<std::mutex> lock(g_LogMutex);
                g_PhotonDetectionLog = finalLog.str();
            }

            g_Notification =
                "Automation finished. Success: " +
                std::to_string(successCount) +
                ", failed: " +
                std::to_string(failedCount);

            g_AutomationBusy = false;
        }
    );
}

// ============================================================
// ADB DEVICE MANAGER
// ============================================================

void RefreshADBDevices()
{
    std::vector<ADBDevice> previousDevices = g_Devices;

    g_Devices.clear();
    g_SelectedDevice = -1;

    g_ADBStatus = "Checking ADB...";

    std::string output = ExecuteADB(L"devices -l");

    g_ADBOutput = output;

    if (IsADBError(output))
    {
        g_ADBStatus = "ADB error";
        g_Notification = "Cannot execute ADB";
        return;
    }

    std::istringstream stream(output);
    std::string line;

    while (std::getline(stream, line))
    {
        line = Trim(line);

        if (line.empty() ||
            line.find("List of devices") != std::string::npos)
            continue;

        std::istringstream lineStream(line);

        ADBDevice device;

        if (!(lineStream >> device.id >> device.status))
            continue;

        if (device.id == "*")
            continue;

        device.model = GetModelFromLine(line);
        device.selected = false;

        for (const ADBDevice& previous : previousDevices)
        {
            if (previous.id == device.id)
            {
                device.selected = previous.selected;
                break;
            }
        }

        g_Devices.push_back(device);
    }

    if (g_Devices.empty())
    {
        g_ADBStatus = "No devices found";
        g_Notification = "No ADB devices detected";
    }
    else
    {
        g_ADBStatus = "Connected";
        g_Notification = "ADB devices refreshed";
    }
}

// ============================================================
// WINDOW ENUMERATION
// ============================================================

BOOL CALLBACK EnumEmulatorWindows(HWND hwnd, LPARAM)
{
    if (!IsWindowVisible(hwnd))
        return TRUE;

    int length = GetWindowTextLengthW(hwnd);

    if (length <= 0)
        return TRUE;

    std::wstring title(
        static_cast<size_t>(length) + 1,
        L'\0'
    );

    GetWindowTextW(hwnd, title.data(), length + 1);
    title.resize(length);

    bool isEmulator =
        ContainsIgnoreCase(title, L"LDPlayer") ||
        ContainsIgnoreCase(title, L"雷电模拟器");

    if (!isEmulator)
        return TRUE;

    EmulatorWindow item;
    item.handle = hwnd;
    item.title = title;

    g_EmulatorWindows.push_back(item);

    return TRUE;
}

void RefreshEmulatorWindows()
{
    g_EmulatorWindows.clear();
    g_SelectedWindow = -1;

    EnumWindows(EnumEmulatorWindows, 0);

    g_Notification = "Emulator windows refreshed";
}

void RefreshEverything()
{
    RefreshADBDevices();
    RefreshEmulatorWindows();
}

// ============================================================
// IMGUI STYLE
// ============================================================

void SetupImGuiStyle()
{
    ImGuiStyle& style = ImGui::GetStyle();

    style.WindowRounding = 10.0f;
    style.ChildRounding = 9.0f;
    style.FrameRounding = 6.0f;
    style.PopupRounding = 6.0f;
    style.ScrollbarRounding = 8.0f;
    style.GrabRounding = 6.0f;
    style.TabRounding = 6.0f;

    style.WindowPadding = ImVec2(16, 16);
    style.FramePadding = ImVec2(10, 7);
    style.ItemSpacing = ImVec2(10, 10);

    style.Colors[ImGuiCol_WindowBg] =
        ImVec4(0.055f, 0.065f, 0.085f, 1.0f);

    style.Colors[ImGuiCol_ChildBg] =
        ImVec4(0.075f, 0.085f, 0.110f, 1.0f);

    style.Colors[ImGuiCol_PopupBg] =
        ImVec4(0.075f, 0.085f, 0.110f, 1.0f);

    style.Colors[ImGuiCol_Border] =
        ImVec4(0.16f, 0.18f, 0.23f, 1.0f);

    style.Colors[ImGuiCol_FrameBg] =
        ImVec4(0.11f, 0.13f, 0.17f, 1.0f);

    style.Colors[ImGuiCol_FrameBgHovered] =
        ImVec4(0.16f, 0.20f, 0.27f, 1.0f);

    style.Colors[ImGuiCol_FrameBgActive] =
        ImVec4(0.19f, 0.25f, 0.34f, 1.0f);

    style.Colors[ImGuiCol_Button] =
        ImVec4(0.13f, 0.34f, 0.65f, 1.0f);

    style.Colors[ImGuiCol_ButtonHovered] =
        ImVec4(0.18f, 0.43f, 0.78f, 1.0f);

    style.Colors[ImGuiCol_ButtonActive] =
        ImVec4(0.10f, 0.29f, 0.55f, 1.0f);

    style.Colors[ImGuiCol_Header] =
        ImVec4(0.12f, 0.28f, 0.48f, 1.0f);

    style.Colors[ImGuiCol_HeaderHovered] =
        ImVec4(0.16f, 0.36f, 0.59f, 1.0f);

    style.Colors[ImGuiCol_HeaderActive] =
        ImVec4(0.18f, 0.40f, 0.68f, 1.0f);

    style.Colors[ImGuiCol_CheckMark] =
        ImVec4(0.30f, 0.65f, 1.0f, 1.0f);

    style.Colors[ImGuiCol_SliderGrab] =
        ImVec4(0.25f, 0.55f, 0.90f, 1.0f);

    style.Colors[ImGuiCol_SliderGrabActive] =
        ImVec4(0.35f, 0.68f, 1.0f, 1.0f);
}

// ============================================================
// UI HELPERS
// ============================================================

void DrawSectionTitle(
    const char* title,
    const char* subtitle)
{
    ImGui::TextColored(
        ImVec4(0.35f, 0.67f, 1.0f, 1.0f),
        "%s",
        title
    );

    ImGui::TextDisabled("%s", subtitle);

    ImGui::Spacing();
    ImGui::Separator();
    ImGui::Spacing();
}

void DrawStatCard(
    const char* title,
    const char* value,
    const char* description)
{
    ImGui::BeginChild(title, ImVec2(0, 105), true);

    ImGui::TextDisabled("%s", title);
    ImGui::Spacing();

    ImGui::SetWindowFontScale(1.35f);

    ImGui::TextColored(
        ImVec4(0.35f, 0.68f, 1.0f, 1.0f),
        "%s",
        value
    );

    ImGui::SetWindowFontScale(1.0f);

    ImGui::TextDisabled("%s", description);

    ImGui::EndChild();
}

// ============================================================
// DASHBOARD
// ============================================================

void DrawDashboard()
{
    DrawSectionTitle(
        "DASHBOARD",
        "SmartClick control center"
    );

    ImGui::Columns(3, nullptr, false);

    DrawStatCard(
        "ADB DEVICES",
        std::to_string(g_Devices.size()).c_str(),
        "Detected devices"
    );

    ImGui::NextColumn();

    DrawStatCard(
        "EMULATOR WINDOWS",
        std::to_string(g_EmulatorWindows.size()).c_str(),
        "Detected windows"
    );

    ImGui::NextColumn();

    DrawStatCard(
        "ADB STATUS",
        g_ADBStatus.c_str(),
        "Connection status"
    );

    ImGui::Columns(1);

    ImGui::Spacing();

    ImGui::BeginChild(
        "DashboardActivity",
        ImVec2(0, 0),
        true
    );

    ImGui::Text("Quick actions");
    ImGui::Spacing();

    if (ImGui::Button("Refresh all", ImVec2(150, 35)))
        RefreshEverything();

    ImGui::SameLine();

    if (ImGui::Button("Refresh ADB", ImVec2(150, 35)))
        RefreshADBDevices();

    ImGui::SameLine();

    if (ImGui::Button("Refresh windows", ImVec2(150, 35)))
        RefreshEmulatorWindows();

    ImGui::Spacing();
    ImGui::Separator();
    ImGui::Spacing();

    ImGui::Text("Recent activity:");
    ImGui::TextDisabled("%s", g_Notification.c_str());

    ImGui::EndChild();
}

// ============================================================
// EMULATOR MANAGER
// ============================================================

void DrawEmulatorManager()
{
    DrawSectionTitle(
        "EMULATOR MANAGER",
        "Manage LDPlayer windows and ADB devices"
    );

    if (ImGui::Button("Refresh everything", ImVec2(190, 35)))
        RefreshEverything();

    ImGui::SameLine();

    if (ImGui::Button("Refresh ADB", ImVec2(130, 35)))
        RefreshADBDevices();

    ImGui::SameLine();

    if (ImGui::Button("Refresh windows", ImVec2(150, 35)))
        RefreshEmulatorWindows();

    ImGui::Spacing();

    ImGui::BeginChild(
        "ADBDevicesPanel",
        ImVec2(0, 210),
        true
    );

    ImGui::Text("ADB DEVICES");
    ImGui::Separator();

    int selectedCount = 0;

    for (const ADBDevice& device : g_Devices)
    {
        if (device.selected)
            selectedCount++;
    }

    ImGui::Text(
        "Selected devices: %d / %d",
        selectedCount,
        static_cast<int>(g_Devices.size())
    );

    ImGui::Spacing();

    if (ImGui::Button("Select all", ImVec2(120, 30)))
    {
        for (ADBDevice& device : g_Devices)
            device.selected = true;

        g_Notification = "All ADB devices selected";
    }

    ImGui::SameLine();

    if (ImGui::Button("Deselect all", ImVec2(140, 30)))
    {
        for (ADBDevice& device : g_Devices)
            device.selected = false;

        g_Notification = "ADB selection cleared";
    }

    ImGui::Spacing();
    ImGui::Separator();

    if (g_Devices.empty())
    {
        ImGui::TextDisabled("No ADB devices found.");
    }
    else
    {
        for (int i = 0; i < static_cast<int>(g_Devices.size()); ++i)
        {
            ADBDevice& device = g_Devices[i];

            ImGui::PushID(device.id.c_str());

            ImGui::Checkbox("##device_selected", &device.selected);

            ImGui::SameLine();

            ImGui::Text(
                "%s [%s]",
                device.id.c_str(),
                device.status.c_str()
            );

            ImGui::SameLine();

            ImGui::TextDisabled("| %s", device.model.c_str());

            ImGui::PopID();
        }
    }

    ImGui::EndChild();

    ImGui::Spacing();

    ImGui::BeginChild(
        "SelectedDevicesPanel",
        ImVec2(0, 170),
        true
    );

    ImGui::Text("SELECTED DEVICES");
    ImGui::Separator();

    selectedCount = 0;

    for (const ADBDevice& device : g_Devices)
    {
        if (device.selected)
            selectedCount++;
    }

    ImGui::Text("Currently selected: %d", selectedCount);
    ImGui::Spacing();

    if (selectedCount == 0)
    {
        ImGui::TextDisabled(
            "No devices selected. Select devices above."
        );
    }
    else
    {
        for (const ADBDevice& device : g_Devices)
        {
            if (!device.selected)
                continue;

            ImGui::BulletText("%s", device.id.c_str());

            ImGui::SameLine();

            ImGui::TextDisabled("[%s]", device.status.c_str());
        }
    }

    ImGui::EndChild();

    ImGui::Spacing();

    ImGui::BeginChild(
        "WindowsPanel",
        ImVec2(0, 150),
        true
    );

    ImGui::Text("LDPLAYER WINDOWS");
    ImGui::Separator();

    if (g_EmulatorWindows.empty())
    {
        ImGui::TextDisabled("No LDPlayer windows found.");
    }
    else
    {
        for (int i = 0; i < static_cast<int>(g_EmulatorWindows.size()); ++i)
        {
            const EmulatorWindow& currentWindow =
                g_EmulatorWindows[i];

            std::string windowLabel =
                WideToUtf8(currentWindow.title);

            ImGui::PushID(i);

            if (ImGui::Selectable(
                windowLabel.c_str(),
                g_SelectedWindow == i))
            {
                g_SelectedWindow = i;
            }

            ImGui::PopID();
        }
    }

    ImGui::EndChild();
}

// ============================================================
// PLACEHOLDER PAGES
// ============================================================

void DrawMacroRecorder()
{
    DrawSectionTitle(
        "MACRO RECORDER",
        "Record and manage automation sequences"
    );

    ImGui::TextDisabled(
        "Macro Recorder module will be implemented next."
    );
}

void DrawVisionEngine()
{
    DrawSectionTitle(
        "VISION ENGINE",
        "Image recognition and visual automation"
    );

    ImGui::TextDisabled(
        "Vision Engine module will be implemented next."
    );
}

// ============================================================
// AUTO LAUNCH
// ============================================================

void DrawAutoLaunch()
{
    DrawSectionTitle(
        "PHOTON AUTO LAUNCH",
        "Launch PHOTON on selected LDPlayer emulators"
    );

    int selectedCount = 0;

    for (const ADBDevice& device : g_Devices)
    {
        if (device.selected)
            selectedCount++;
    }

    ImGui::BeginChild(
        "PhotonLaunchInfo",
        ImVec2(0, 115),
        true
    );

    ImGui::Text("SELECTED EMULATORS");
    ImGui::Spacing();

    ImGui::SetWindowFontScale(1.4f);

    ImGui::TextColored(
        ImVec4(0.30f, 0.70f, 1.0f, 1.0f),
        "%d",
        selectedCount
    );

    ImGui::SetWindowFontScale(1.0f);
    ImGui::SameLine();

    ImGui::TextDisabled(
        "/ %d devices available",
        static_cast<int>(g_Devices.size())
    );

    ImGui::EndChild();

    ImGui::Spacing();

    // --------------------------------------------------------
    // START PHOTON - ORIGINAL LAUNCH MECHANISM
    // --------------------------------------------------------

    ImGui::BeginChild(
        "PhotonLaunchControl",
        ImVec2(0, 145),
        true
    );

    ImGui::Text("PHOTON CONTROL");
    ImGui::Spacing();

    ImGui::TextDisabled(
        "Launch PHOTON on every selected emulator."
    );

    ImGui::Spacing();

    if (ImGui::Button("START PHOTON", ImVec2(220, 48)))
    {
        g_PhotonLaunchLog.clear();

        if (selectedCount == 0)
        {
            g_PhotonLaunchLog =
                "ERROR: No ADB devices selected.";

            g_Notification =
                "Select at least one ADB device.";
        }
        else
        {
            int launchedCount = 0;
            int skippedCount = 0;

            for (const ADBDevice& device : g_Devices)
            {
                if (!device.selected)
                    continue;

                g_PhotonLaunchLog +=
                    "\n[" + device.id + "] ";

                if (device.status != "device")
                {
                    g_PhotonLaunchLog +=
                        "SKIPPED - device is not ready.\n";

                    skippedCount++;
                    continue;
                }

                g_PhotonLaunchLog +=
                    "Sending launch command...\n";

                std::wstring arguments =
                    L"-s " + DeviceArgument(device.id) +
                    L" shell monkey -p com.photon.top "
                    L"-c android.intent.category.LAUNCHER 1";

                std::string output = ExecuteADB(arguments);

                if (IsADBError(output))
                {
                    g_PhotonLaunchLog +=
                        "ERROR: " + output + "\n";

                    skippedCount++;
                }
                else
                {
                    g_PhotonLaunchLog += output;

                    if (output.empty())
                        g_PhotonLaunchLog +=
                        "ADB returned empty output.\n";

                    launchedCount++;
                }
            }

            g_Notification =
                "Photon launch commands sent: " +
                std::to_string(launchedCount) +
                ", skipped: " +
                std::to_string(skippedCount);
        }
    }

    ImGui::EndChild();

    ImGui::Spacing();

    // --------------------------------------------------------
    // PHOTON AUTOMATION
    // --------------------------------------------------------

    ImGui::BeginChild(
        "PhotonDetectionPanel",
        ImVec2(0, 0),
        true
    );

    ImGui::Text("PHOTON AUTOMATION");
    ImGui::Spacing();

    ImGui::TextDisabled(
        "Login, random roleplay names, registration and next steps."
    );

    ImGui::Spacing();

    if (g_TemplatesLoaded)
    {
        ImGui::TextColored(
            ImVec4(0.30f, 0.80f, 0.45f, 1.0f),
            "Login templates loaded."
        );
    }
    else
    {
        ImGui::TextColored(
            ImVec4(1.0f, 0.35f, 0.30f, 1.0f),
            "Login templates are missing."
        );
    }

    if (AreAllStageTemplatesLoaded())
    {
        ImGui::TextColored(
            ImVec4(0.30f, 0.80f, 0.45f, 1.0f),
            "All registration templates loaded."
        );
    }
    else
    {
        ImGui::TextColored(
            ImVec4(1.0f, 0.65f, 0.25f, 1.0f),
            "Some registration templates are missing."
        );
    }

    ImGui::Spacing();

    if (ImGui::Button(
        "RELOAD TEMPLATES",
        ImVec2(220, 35)))
    {
        if (!g_AutomationBusy.load())
        {
            LoadPhotonTemplates();

            g_Notification =
                "Template reload completed.";
        }
    }

    ImGui::Spacing();
    ImGui::Separator();
    ImGui::Spacing();

    ImGui::Text("REGISTRATION PASSWORD");

    ImGui::SetNextItemWidth(300);

    ImGui::InputText(
        "##registration_password",
        g_RegistrationPassword,
        sizeof(g_RegistrationPassword),
        ImGuiInputTextFlags_Password
    );

    ImGui::TextDisabled(
        "English letters and digits only."
    );

    ImGui::Spacing();

    ImGui::TextWrapped(
        "Each selected emulator runs its own automation worker. "
        "Every next button is detected before clicking."
    );

    ImGui::Spacing();

    if (g_AutomationBusy.load())
    {
        ImGui::BeginDisabled();

        ImGui::Button(
            "AUTOMATION RUNNING...",
            ImVec2(260, 48)
        );

        ImGui::EndDisabled();

        ImGui::SameLine();

        ImGui::TextColored(
            ImVec4(0.30f, 0.80f, 0.45f, 1.0f),
            "Working in background..."
        );
    }
    else
    {
        if (ImGui::Button(
            "START FULL AUTOMATION",
            ImVec2(260, 48)))
        {
            StartPhotonAutomation();
        }
    }

    ImGui::Spacing();
    ImGui::Separator();
    ImGui::Spacing();

    ImGui::Text("TEMPLATE STATUS");

    ImGui::BeginChild(
        "TemplateStatusPanel",
        ImVec2(0, 145),
        true
    );

    ImGui::TextWrapped("%s", g_TemplateStatus.c_str());

    ImGui::EndChild();

    ImGui::Spacing();

    ImGui::Text("AUTOMATION LOG");

    std::string detectionLogCopy;

    {
        std::lock_guard<std::mutex> lock(g_LogMutex);
        detectionLogCopy = g_PhotonDetectionLog;
    }

    ImGui::BeginChild(
        "PhotonDetectionLog",
        ImVec2(0, 260),
        true
    );

    if (detectionLogCopy.empty())
    {
        ImGui::TextDisabled(
            "Automation results will appear here."
        );
    }
    else
    {
        ImGui::TextWrapped(
            "%s",
            detectionLogCopy.c_str()
        );
    }

    ImGui::EndChild();

    ImGui::Spacing();

    ImGui::BeginChild(
        "PhotonLaunchLog",
        ImVec2(0, 0),
        true
    );

    ImGui::Text("LAUNCH LOG");
    ImGui::Separator();

    if (g_PhotonLaunchLog.empty())
    {
        ImGui::TextDisabled(
            "Waiting for launch command..."
        );
    }
    else
    {
        ImGui::TextWrapped(
            "%s",
            g_PhotonLaunchLog.c_str()
        );
    }

    ImGui::EndChild();

    ImGui::EndChild();
}

// ============================================================
// SETTINGS
// ============================================================

void DrawSettings()
{
    DrawSectionTitle(
        "SETTINGS",
        "Application configuration"
    );

    ImGui::Text("ADB executable:");
    ImGui::TextWrapped("%ls", ADB_PATH);

    ImGui::Spacing();
    ImGui::Separator();
    ImGui::Spacing();

    ImGui::Text("PHOTON template files:");

    const char* filenames[] =
    {
        "photon_ready.png",
        "photon_after_login.png",
        "play.png",
        "password.png",
        "password_repeat.png",
        "register.png",
        "skip.png",
        "next.png",
        "start.png",
        "enter_name.png",
        "enter_lastname.png"
    };

    for (const char* filename : filenames)
    {
        std::wstring path = GetTemplatePath(
            Utf8ToWide(filename)
        );

        std::string utf8Path = WideToUtf8(path);

        ImGui::BulletText("%s", filename);
        ImGui::TextWrapped("%s", utf8Path.c_str());
    }

    ImGui::Spacing();
    ImGui::Separator();
    ImGui::Spacing();

    ImGui::Text("Registration password:");

    ImGui::SetNextItemWidth(300);

    ImGui::InputText(
        "##settings_password",
        g_RegistrationPassword,
        sizeof(g_RegistrationPassword),
        ImGuiInputTextFlags_Password
    );

    ImGui::TextDisabled(
        "Use English letters and digits only."
    );

    ImGui::Spacing();

    ImGui::Text("Template status:");

    ImGui::TextWrapped(
        "%s",
        g_TemplateStatus.c_str()
    );

    if (ImGui::Button(
        "Reload PHOTON templates",
        ImVec2(230, 35)))
    {
        if (!g_AutomationBusy.load())
        {
            LoadPhotonTemplates();

            g_Notification =
                "Template reload completed.";
        }
    }
}

// ============================================================
// LOGS
// ============================================================

void DrawLogs()
{
    DrawSectionTitle(
        "LOGS",
        "Application activity"
    );

    ImGui::TextWrapped("%s", g_Notification.c_str());

    ImGui::Spacing();

    ImGui::Text("Last ADB output:");

    ImGui::BeginChild(
        "ADBLogOutput",
        ImVec2(0, 0),
        true
    );

    ImGui::TextWrapped("%s", g_ADBOutput.c_str());

    ImGui::EndChild();
}

// ============================================================
// SIDEBAR
// ============================================================

void DrawSidebar()
{
    ImGui::BeginChild(
        "Sidebar",
        ImVec2(205, 0),
        true
    );

    ImGui::Spacing();

    ImGui::SetWindowFontScale(1.35f);

    ImGui::TextColored(
        ImVec4(0.30f, 0.65f, 1.0f, 1.0f),
        "SMARTCLICK"
    );

    ImGui::SetWindowFontScale(1.0f);

    ImGui::TextDisabled("PREMIUM GAMING");

    ImGui::Spacing();
    ImGui::Separator();
    ImGui::Spacing();

    for (int i = 0; i < IM_ARRAYSIZE(g_PageNames); ++i)
    {
        if (ImGui::Selectable(
            g_PageNames[i],
            g_CurrentPage == i,
            0,
            ImVec2(0, 38)))
        {
            g_CurrentPage = i;
        }
    }

    ImGui::SetCursorPosY(
        ImGui::GetWindowHeight() - 55
    );

    ImGui::Separator();
    ImGui::TextDisabled("SmartClick v1.3.0");

    ImGui::EndChild();
}

// ============================================================
// MAIN INTERFACE
// ============================================================

void DrawMainInterface()
{
    ImGui::SetNextWindowPos(ImVec2(0, 0));

    ImGui::SetNextWindowSize(
        ImGui::GetIO().DisplaySize
    );

    ImGui::Begin(
        "SmartClick",
        nullptr,
        ImGuiWindowFlags_NoDecoration |
        ImGuiWindowFlags_NoMove |
        ImGuiWindowFlags_NoResize |
        ImGuiWindowFlags_NoSavedSettings
    );

    DrawSidebar();

    ImGui::SameLine();

    ImGui::BeginChild(
        "MainContent",
        ImVec2(0, 0),
        false
    );

    ImGui::Spacing();

    switch (g_CurrentPage)
    {
    case 0:
        DrawDashboard();
        break;

    case 1:
        DrawMacroRecorder();
        break;

    case 2:
        DrawVisionEngine();
        break;

    case 3:
        DrawEmulatorManager();
        break;

    case 4:
        DrawAutoLaunch();
        break;

    case 5:
        DrawSettings();
        break;

    case 6:
        DrawLogs();
        break;
    }

    ImGui::EndChild();
    ImGui::End();
}

// ============================================================
// DIRECTX HELPERS
// ============================================================

void CreateRenderTarget()
{
    ID3D11Texture2D* backBuffer = nullptr;

    if (SUCCEEDED(
        g_pSwapChain->GetBuffer(
            0,
            IID_PPV_ARGS(&backBuffer))))
    {
        g_pd3dDevice->CreateRenderTargetView(
            backBuffer,
            nullptr,
            &g_mainRenderTargetView
        );

        backBuffer->Release();
    }
}

void CleanupRenderTarget()
{
    if (g_mainRenderTargetView)
    {
        g_mainRenderTargetView->Release();
        g_mainRenderTargetView = nullptr;
    }
}

bool CreateDeviceD3D(HWND hwnd)
{
    DXGI_SWAP_CHAIN_DESC swapChainDesc{};

    swapChainDesc.BufferCount = 2;

    swapChainDesc.BufferDesc.Format =
        DXGI_FORMAT_R8G8B8A8_UNORM;

    swapChainDesc.BufferDesc.RefreshRate.Numerator = 60;
    swapChainDesc.BufferDesc.RefreshRate.Denominator = 1;

    swapChainDesc.Flags =
        DXGI_SWAP_CHAIN_FLAG_ALLOW_MODE_SWITCH;

    swapChainDesc.BufferUsage =
        DXGI_USAGE_RENDER_TARGET_OUTPUT;

    swapChainDesc.OutputWindow = hwnd;
    swapChainDesc.SampleDesc.Count = 1;
    swapChainDesc.Windowed = TRUE;
    swapChainDesc.SwapEffect = DXGI_SWAP_EFFECT_DISCARD;

    UINT createFlags = 0;

#ifdef _DEBUG
    createFlags |= D3D11_CREATE_DEVICE_DEBUG;
#endif

    D3D_FEATURE_LEVEL featureLevel;

    const D3D_FEATURE_LEVEL featureLevels[] =
    {
        D3D_FEATURE_LEVEL_11_0,
        D3D_FEATURE_LEVEL_10_0
    };

    HRESULT result = D3D11CreateDeviceAndSwapChain(
        nullptr,
        D3D_DRIVER_TYPE_HARDWARE,
        nullptr,
        createFlags,
        featureLevels,
        2,
        D3D11_SDK_VERSION,
        &swapChainDesc,
        &g_pSwapChain,
        &g_pd3dDevice,
        &featureLevel,
        &g_pd3dDeviceContext
    );

    if (result == DXGI_ERROR_UNSUPPORTED)
    {
        result = D3D11CreateDeviceAndSwapChain(
            nullptr,
            D3D_DRIVER_TYPE_WARP,
            nullptr,
            createFlags,
            featureLevels,
            2,
            D3D11_SDK_VERSION,
            &swapChainDesc,
            &g_pSwapChain,
            &g_pd3dDevice,
            &featureLevel,
            &g_pd3dDeviceContext
        );
    }

    if (FAILED(result))
        return false;

    CreateRenderTarget();

    return true;
}

void CleanupDeviceD3D()
{
    CleanupRenderTarget();

    if (g_pSwapChain)
    {
        g_pSwapChain->Release();
        g_pSwapChain = nullptr;
    }

    if (g_pd3dDeviceContext)
    {
        g_pd3dDeviceContext->Release();
        g_pd3dDeviceContext = nullptr;
    }

    if (g_pd3dDevice)
    {
        g_pd3dDevice->Release();
        g_pd3dDevice = nullptr;
    }
}

// ============================================================
// WINDOW PROCEDURE
// ============================================================

extern IMGUI_IMPL_API LRESULT
ImGui_ImplWin32_WndProcHandler(
    HWND hWnd,
    UINT msg,
    WPARAM wParam,
    LPARAM lParam
);

LRESULT WINAPI WndProc(
    HWND hWnd,
    UINT msg,
    WPARAM wParam,
    LPARAM lParam)
{
    if (ImGui_ImplWin32_WndProcHandler(
        hWnd,
        msg,
        wParam,
        lParam))
    {
        return true;
    }

    switch (msg)
    {
    case WM_SIZE:
        if (g_pd3dDevice != nullptr &&
            wParam != SIZE_MINIMIZED)
        {
            CleanupRenderTarget();

            g_pSwapChain->ResizeBuffers(
                0,
                LOWORD(lParam),
                HIWORD(lParam),
                DXGI_FORMAT_UNKNOWN,
                0
            );

            CreateRenderTarget();
        }

        return 0;

    case WM_SYSCOMMAND:
        if ((wParam & 0xfff0) == SC_KEYMENU)
            return 0;

        break;

    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;
    }

    return DefWindowProcW(
        hWnd,
        msg,
        wParam,
        lParam
    );
}

// ============================================================
// ENTRY POINT
// ============================================================

int WINAPI WinMain(
    HINSTANCE hInstance,
    HINSTANCE,
    LPSTR,
    int)
{
    WNDCLASSEXW wc{};

    wc.cbSize = sizeof(WNDCLASSEXW);
    wc.style = CS_CLASSDC;
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInstance;
    wc.lpszClassName = L"SmartClickWindow";

    RegisterClassExW(&wc);

    g_hWnd = CreateWindowW(
        wc.lpszClassName,
        L"SmartClick Premium",
        WS_OVERLAPPEDWINDOW,
        100,
        100,
        1250,
        800,
        nullptr,
        nullptr,
        wc.hInstance,
        nullptr
    );

    if (!g_hWnd)
    {
        UnregisterClassW(
            wc.lpszClassName,
            wc.hInstance
        );

        return 1;
    }

    if (!CreateDeviceD3D(g_hWnd))
    {
        CleanupDeviceD3D();

        UnregisterClassW(
            wc.lpszClassName,
            wc.hInstance
        );

        return 1;
    }

    ShowWindow(g_hWnd, SW_SHOWDEFAULT);
    UpdateWindow(g_hWnd);

    IMGUI_CHECKVERSION();

    ImGui::CreateContext();

    ImGuiIO& io = ImGui::GetIO();

    io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard;

    SetupImGuiStyle();

    ImGui_ImplWin32_Init(g_hWnd);

    ImGui_ImplDX11_Init(
        g_pd3dDevice,
        g_pd3dDeviceContext
    );

    LoadPhotonTemplates();
    RefreshEverything();

    MSG msg{};

    while (g_Running)
    {
        while (PeekMessageW(
            &msg,
            nullptr,
            0U,
            0U,
            PM_REMOVE))
        {
            TranslateMessage(&msg);
            DispatchMessageW(&msg);

            if (msg.message == WM_QUIT)
                g_Running = false;
        }

        if (!g_Running)
            break;

        ImGui_ImplDX11_NewFrame();
        ImGui_ImplWin32_NewFrame();

        ImGui::NewFrame();

        DrawMainInterface();

        ImGui::Render();

        const float clearColor[4] =
        {
            0.035f,
            0.045f,
            0.065f,
            1.0f
        };

        g_pd3dDeviceContext->OMSetRenderTargets(
            1,
            &g_mainRenderTargetView,
            nullptr
        );

        g_pd3dDeviceContext->ClearRenderTargetView(
            g_mainRenderTargetView,
            clearColor
        );

        ImGui_ImplDX11_RenderDrawData(
            ImGui::GetDrawData()
        );

        g_pSwapChain->Present(1, 0);
    }

    if (g_AutomationThread.joinable())
        g_AutomationThread.join();

    ImGui_ImplDX11_Shutdown();
    ImGui_ImplWin32_Shutdown();

    ImGui::DestroyContext();

    CleanupDeviceD3D();

    DestroyWindow(g_hWnd);

    UnregisterClassW(
        wc.lpszClassName,
        wc.hInstance
    );

    return 0;
}
