
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX

#ifndef _WIN32_WINNT
#define _WIN32_WINNT 0x0601
#endif

#include <windows.h>
#include <d3d11.h>
#include <tchar.h>

#include <shlobj.h>
#include <string>
#include <vector>
#include <sstream>
#include <algorithm>
#include <future>
#include <exception>
#include <cstdint>
#include <cwctype>
#include <thread>
#include <atomic>
#include <mutex>
#include <chrono>
#include <random>
#include <cctype>
#include <cmath>
#include <map>
#include <array>
#include <unordered_set>

#include "imgui.h"
#include "imgui_impl_win32.h"
#include "imgui_impl_dx11.h"

#include <opencv2/imgcodecs.hpp>
#include <opencv2/imgproc.hpp>

#ifdef _MSC_VER
#pragma comment(lib, "shell32.lib")
#pragma comment(lib, "d3d11.lib")
#pragma comment(lib, "dxgi.lib")
#pragma comment(lib, "d3dcompiler.lib")
#endif

// ============================================================
// CONFIGURATION
// ============================================================

static const wchar_t* ADB_PATH =
L"C:\\LDPlayer\\LDPlayer9\\adb.exe";

static constexpr double PHOTON_MATCH_THRESHOLD = 0.86;
static constexpr int SCREEN_WIDTH = 960;
static constexpr int SCREEN_HEIGHT = 540;

static constexpr int LOGIN_TIMEOUT_MS = 15000;
static constexpr int AFTER_LOGIN_TIMEOUT_MS = 8000;

// Максимальное ожидание появления каждого последующего шаблона.
static constexpr int STAGE_TIMEOUT_MS = 30000;

// Интервал между проверками изображения.
static constexpr int DETECTION_INTERVAL_MS = 120;

// Пауза перед первым действием.
static constexpr int INITIAL_DELAY_MS = 350;

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
static int g_SelectedWindow = -1;

static std::atomic<bool> g_AutomationBusy{ false };
static std::atomic<bool> g_CancelAutomation{ false };
static std::atomic<bool> g_ShutdownRequested{ false };
static std::thread g_AutomationThread;
static std::string g_AutomationNotification;

struct AdbJobResult
{
    bool launch = false;
    std::string output;
    std::string notification;
};

static std::future<AdbJobResult> g_ADBJob;
static std::mutex g_LogMutex;

static char g_RegistrationPassword[128]{};

bool IsAutomationCancelled()
{
    return g_CancelAutomation || g_ShutdownRequested;
}

bool PauseAutomation(DWORD milliseconds)
{
    const ULONGLONG deadline = GetTickCount64() + milliseconds;
    while (!IsAutomationCancelled())
    {
        const ULONGLONG now = GetTickCount64();
        if (now >= deadline)
            return true;

        Sleep(static_cast<DWORD>(std::min<ULONGLONG>(20, deadline - now)));
    }
    return false;
}

DWORD RemainingTime(ULONGLONG deadline)
{
    const ULONGLONG now = GetTickCount64();
    return now < deadline
        ? static_cast<DWORD>(std::min<ULONGLONG>(deadline - now, MAXDWORD))
        : 0;
}

static void AppendPhotonLog(const char* data, size_t length)
{
    std::lock_guard<std::mutex> lock(g_LogMutex);
    g_PhotonDetectionLog.append(data, length);

    constexpr size_t limit = 256 * 1024;
    if (g_PhotonDetectionLog.size() > limit)
    {
        const size_t excess = g_PhotonDetectionLog.size() - limit;
        const size_t newline = g_PhotonDetectionLog.find('\n', excess);
        g_PhotonDetectionLog.erase(0, newline == std::string::npos ? excess : newline + 1);
    }
}

static void AppendPhotonLog(const std::string& message)
{
    AppendPhotonLog(message.data(), message.size());
}

// Streams worker-thread log output directly into the UI-visible log.
// Every write is protected so the render thread can safely take a snapshot.
class LivePhotonLogBuffer : public std::streambuf
{
protected:
    std::streamsize xsputn(
        const char* data,
        std::streamsize count) override
    {
        if (data && count > 0)
        {
            AppendPhotonLog(data, static_cast<size_t>(count));
        }

        return count;
    }

    int_type overflow(int_type character) override
    {
        if (!traits_type::eq_int_type(
            character,
            traits_type::eof()))
        {
            const char value =
                traits_type::to_char_type(character);

            AppendPhotonLog(&value, 1);
        }

        return traits_type::not_eof(character);
    }

    int sync() override
    {
        return 0;
    }
};

// ============================================================
// IMAGE TEMPLATES
// ============================================================

static const std::array<std::string, 9> g_RegistrationTemplates =
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
static bool g_Minimized = false;
static UINT g_PendingWidth = 0;
static UINT g_PendingHeight = 0;

// ============================================================
// DATA
// ============================================================

struct ADBDevice
{
    std::string id;
    std::string status;
    std::string model;
    bool selected = false;
    HWND automationWindow = nullptr;
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

// Real Win32 input is global to the desktop, so automation is serialized.
// Each ADB device is explicitly mapped to its visible LDPlayer top-level HWND.
static std::mutex g_DeviceWindowMapMutex;
struct WindowIdentity
{
    HWND handle = nullptr;
    DWORD processId = 0;
};
static std::map<std::string, WindowIdentity> g_DeviceWindowMap;

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

class UniqueHandle
{
public:
    explicit UniqueHandle(HANDLE handle) : handle_(handle) {}
    ~UniqueHandle() { reset(nullptr); }

    UniqueHandle(const UniqueHandle&) = delete;
    UniqueHandle& operator=(const UniqueHandle&) = delete;

    HANDLE get() const { return handle_; }

    void reset(HANDLE handle)
    {
        if (handle_ && handle_ != INVALID_HANDLE_VALUE)
            CloseHandle(handle_);
        handle_ = handle;
    }

private:
    HANDLE handle_;
};

std::wstring ReadEnvironmentVariable(const wchar_t* name)
{
    const DWORD capacity = GetEnvironmentVariableW(name, nullptr, 0);
    if (!capacity)
        return {};

    std::wstring value(capacity, L'\0');
    const DWORD length = GetEnvironmentVariableW(name, value.data(), capacity);
    if (!length || length >= capacity)
        return {};

    value.resize(length);
    return value;
}

std::wstring ResolveADBPath()
{
    std::wstring configured = ReadEnvironmentVariable(L"SMARTCLICK_ADB_PATH");
    if (!configured.empty())
        return configured;

    const DWORD attributes = GetFileAttributesW(ADB_PATH);
    if (attributes != INVALID_FILE_ATTRIBUTES && !(attributes & FILE_ATTRIBUTE_DIRECTORY))
        return ADB_PATH;

    const std::wstring path = ReadEnvironmentVariable(L"PATH");
    if (!path.empty())
    {
        std::wstring found(32768, L'\0');
        const DWORD length = SearchPathW(
            path.c_str(), L"adb.exe", nullptr,
            static_cast<DWORD>(found.size()), found.data(), nullptr);
        if (length && length < found.size())
        {
            found.resize(length);
            return found;
        }
    }

    return {};
}

const std::wstring& ADBExecutable()
{
    static const std::wstring path = ResolveADBPath();
    return path;
}

std::wstring QuoteProcessArgument(const std::wstring& argument)
{
    std::wstring quoted = L"\"";
    size_t backslashes = 0;
    for (wchar_t character : argument)
    {
        if (character == L'\\')
        {
            ++backslashes;
            continue;
        }

        if (character == L'"')
            quoted.append(backslashes + 1, L'\\');
        quoted.append(backslashes, L'\\');
        quoted.push_back(character);
        backslashes = 0;
    }

    quoted.append(backslashes * 2, L'\\');
    quoted.push_back(L'"');
    return quoted;
}

std::string Win32Error(const char* operation)
{
    const DWORD error = GetLastError();
    return std::string(operation) + " (Win32 error " + std::to_string(error) + ").";
}

bool RunProcess(
    const std::wstring& executable,
    const std::wstring& arguments,
    std::vector<unsigned char>& output,
    std::string& diagnostic,
    DWORD timeoutMs,
    bool captureStderr = true,
    bool automation = false)
{
    output.clear();
    diagnostic.clear();
    if (executable.empty())
    {
        diagnostic = "ADB executable not found. Set SMARTCLICK_ADB_PATH to adb.exe.";
        return false;
    }

    if (g_ShutdownRequested || (automation && g_CancelAutomation))
    {
        diagnostic = "ADB command cancelled.";
        return false;
    }

    std::wstring command = QuoteProcessArgument(executable) + L" " + arguments;
    UniqueHandle readHandle(nullptr);
    PROCESS_INFORMATION process{};
    {
        // Close inheritable handles before allowing another child to start.
        static std::mutex launchMutex;
        std::lock_guard<std::mutex> lock(launchMutex);

        SECURITY_ATTRIBUTES security{ sizeof(security), nullptr, TRUE };
        HANDLE readPipe = nullptr;
        HANDLE writePipe = nullptr;
        if (!CreatePipe(&readPipe, &writePipe, &security, 0))
        {
            diagnostic = Win32Error("Cannot create ADB output pipe");
            return false;
        }
        readHandle.reset(readPipe);
        const UniqueHandle writeHandle(writePipe);

        const bool nonInheritable =
            SetHandleInformation(readPipe, HANDLE_FLAG_INHERIT, 0) != FALSE;
        if (!nonInheritable)
        {
            diagnostic = Win32Error("Cannot configure ADB output pipe");
            return false;
        }

        const UniqueHandle nullHandle(CreateFileW(
            L"NUL", GENERIC_READ | GENERIC_WRITE,
            FILE_SHARE_READ | FILE_SHARE_WRITE, &security,
            OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, nullptr));
        if (nullHandle.get() == INVALID_HANDLE_VALUE)
        {
            diagnostic = Win32Error("Cannot open NUL for ADB");
            return false;
        }

        STARTUPINFOW startup{};
        startup.cb = sizeof(startup);
        startup.dwFlags = STARTF_USESTDHANDLES;
        startup.hStdInput = nullHandle.get();
        startup.hStdOutput = writeHandle.get();
        startup.hStdError = captureStderr ? writeHandle.get() : nullHandle.get();

        if (!CreateProcessW(executable.c_str(), command.data(), nullptr, nullptr,
            TRUE, CREATE_NO_WINDOW, nullptr, nullptr, &startup, &process))
        {
            diagnostic = Win32Error("Cannot start ADB");
            return false;
        }
    }

    const UniqueHandle processHandle(process.hProcess);
    const UniqueHandle threadHandle(process.hThread);
    const ULONGLONG started = GetTickCount64();
    constexpr size_t maxOutputBytes = 16 * 1024 * 1024;
    unsigned char buffer[16384];
    bool pipeClosed = false;

    for (;;)
    {
        const DWORD waitResult = WaitForSingleObject(processHandle.get(), 0);
        const bool exited = waitResult == WAIT_OBJECT_0;
        if (waitResult == WAIT_FAILED)
        {
            diagnostic = Win32Error("Cannot wait for ADB");
            break;
        }
        if (g_ShutdownRequested || (automation && g_CancelAutomation))
        {
            diagnostic = "ADB command cancelled.";
            break;
        }

        DWORD available = 0;
        if (!pipeClosed && !PeekNamedPipe(readHandle.get(), nullptr, 0, nullptr, &available, nullptr))
        {
            if (GetLastError() != ERROR_BROKEN_PIPE)
            {
                diagnostic = Win32Error("Cannot inspect ADB output pipe");
                break;
            }
            pipeClosed = true;
        }

        if (!available && exited)
        {
            DWORD exitCode = 0;
            if (!GetExitCodeProcess(processHandle.get(), &exitCode))
            {
                diagnostic = Win32Error("Cannot get ADB exit code");
                return false;
            }
            if (exitCode == 0)
                return true;

            diagnostic = "ADB exited with code " + std::to_string(exitCode) + ".";
            return false;
        }

        const ULONGLONG elapsed = GetTickCount64() - started;
        if (elapsed >= timeoutMs)
        {
            diagnostic = "ADB command timed out after " + std::to_string(timeoutMs) + " ms.";
            break;
        }

        if (!available)
        {
            WaitForSingleObject(processHandle.get(),
                static_cast<DWORD>(std::min<ULONGLONG>(5, timeoutMs - elapsed)));
            continue;
        }

        DWORD bytesRead = 0;
        const DWORD requested = std::min<DWORD>(available, sizeof(buffer));
        if (!ReadFile(readHandle.get(), buffer, requested, &bytesRead, nullptr) || !bytesRead)
        {
            diagnostic = Win32Error("Cannot read ADB output");
            break;
        }
        if (bytesRead > maxOutputBytes - output.size())
        {
            diagnostic = "ADB output exceeded 16 MiB.";
            break;
        }
        output.insert(output.end(), buffer, buffer + bytesRead);
    }

    if (WaitForSingleObject(processHandle.get(), 0) == WAIT_TIMEOUT &&
        TerminateProcess(processHandle.get(), 1))
    {
        WaitForSingleObject(processHandle.get(), 250);
    }
    return false;
}

std::string ExecuteADB(
    const std::wstring& arguments,
    DWORD timeoutMs = 10000)
{
    std::vector<unsigned char> data;
    std::string diagnostic;
    const bool success = RunProcess(ADBExecutable(), arguments, data, diagnostic, timeoutMs);
    const std::string output(data.begin(), data.end());

    if (success)
        return output;

    return "ERROR: " + diagnostic + (output.empty() ? "" : "\n" + output);
}

bool IsADBError(const std::string& output)
{
    return output.rfind("ERROR:", 0) == 0;
}

std::wstring DeviceArgument(const std::string& deviceId)
{
    return QuoteProcessArgument(Utf8ToWide(deviceId));
}

// ============================================================
// REAL WINDOWS INPUT (VISIBLE MOUSE + KEYBOARD)
// ============================================================

HWND GetMappedEmulatorWindow(const std::string& deviceId)
{
    std::lock_guard<std::mutex> lock(g_DeviceWindowMapMutex);
    auto it = g_DeviceWindowMap.find(deviceId);

    if (it == g_DeviceWindowMap.end())
        return nullptr;

    const WindowIdentity& identity = it->second;
    DWORD processId = 0;
    GetWindowThreadProcessId(identity.handle, &processId);
    return processId && processId == identity.processId ? identity.handle : nullptr;
}

struct RenderChildSearch
{
    HWND bestWindow = nullptr;
    double bestScore = -1.0;
};

BOOL CALLBACK FindRenderChildCallback(HWND hwnd, LPARAM parameter)
{
    auto* search = reinterpret_cast<RenderChildSearch*>(parameter);

    if (!search || !IsWindowVisible(hwnd))
        return TRUE;

    RECT rc{};
    if (!GetClientRect(hwnd, &rc))
        return TRUE;

    const int width = rc.right - rc.left;
    const int height = rc.bottom - rc.top;

    if (width < 320 || height < 180)
        return TRUE;

    const double ratio = static_cast<double>(width) /
        static_cast<double>(height);

    // The ADB screenshots are 16:9. Prefer the largest visible child
    // whose client area resembles the actual game render surface.
    if (ratio < 1.45 || ratio > 2.05)
        return TRUE;

    const double ratioError = std::abs(std::log(ratio / 1.7777777778));
    const double area = static_cast<double>(width) * height;
    const double score = area / (1.0 + ratioError * 5.0);

    if (score > search->bestScore)
    {
        search->bestScore = score;
        search->bestWindow = hwnd;
    }

    return TRUE;
}

HWND FindEmulatorRenderWindow(HWND topLevelWindow)
{
    if (!IsWindow(topLevelWindow))
        return nullptr;

    RenderChildSearch search;
    EnumChildWindows(
        topLevelWindow,
        FindRenderChildCallback,
        reinterpret_cast<LPARAM>(&search)
    );

    return search.bestWindow ? search.bestWindow : topLevelWindow;
}

bool IsForegroundEmulator(HWND window)
{
    const HWND foreground = GetForegroundWindow();
    return window && foreground && GetAncestor(foreground, GA_ROOT) == window;
}

bool ActivateEmulatorWindow(
    const std::string& deviceId,
    HWND& topLevelWindow,
    HWND& renderWindow,
    std::string& diagnostic)
{
    if (IsAutomationCancelled())
    {
        diagnostic = "Input cancelled.";
        return false;
    }

    topLevelWindow = GetMappedEmulatorWindow(deviceId);

    if (!topLevelWindow || !IsWindow(topLevelWindow))
    {
        diagnostic =
            "No valid LDPlayer window is mapped to ADB device " +
            deviceId +
            ". Assign the matching window in Emulator Manager.";
        return false;
    }

    if (IsHungAppWindow(topLevelWindow))
    {
        diagnostic = "The assigned LDPlayer window is not responding.";
        return false;
    }

    if (IsIconic(topLevelWindow))
    {
        ShowWindowAsync(topLevelWindow, SW_RESTORE);
        for (int attempt = 0; attempt < 25 && IsIconic(topLevelWindow); ++attempt)
        {
            if (!PauseAutomation(20))
            {
                diagnostic = "Input cancelled while restoring LDPlayer.";
                return false;
            }
        }
        if (IsIconic(topLevelWindow))
        {
            diagnostic = "Could not restore the minimized LDPlayer window.";
            return false;
        }
    }

    // Recalculate the actual game surface for every action. The user may
    // freely move or resize LDPlayer windows while automation is running.
    renderWindow = FindEmulatorRenderWindow(topLevelWindow);

    if (!renderWindow || !IsWindow(renderWindow))
    {
        diagnostic = "Could not find the LDPlayer render area.";
        return false;
    }

    SetWindowPos(
        topLevelWindow,
        HWND_TOP,
        0, 0, 0, 0,
        SWP_NOMOVE | SWP_NOSIZE | SWP_SHOWWINDOW | SWP_ASYNCWINDOWPOS
    );

    // Ensure this worker thread has a message queue before attaching input.
    MSG queueMessage{};
    PeekMessageW(
        &queueMessage,
        nullptr,
        WM_USER,
        WM_USER,
        PM_NOREMOVE
    );

    const HWND previousForeground = GetForegroundWindow();
    const DWORD foregroundThreadId = previousForeground
        ? GetWindowThreadProcessId(previousForeground, nullptr)
        : 0;
    const DWORD targetThreadId =
        GetWindowThreadProcessId(topLevelWindow, nullptr);
    const DWORD currentThreadId = GetCurrentThreadId();

    // Attach to both the current foreground queue and LDPlayer's queue.
    // This is important when switching between several separate emulator windows.
    bool attachedForeground = false;
    bool attachedTarget = false;

    if (foregroundThreadId != 0 &&
        foregroundThreadId != currentThreadId)
    {
        attachedForeground = AttachThreadInput(
            currentThreadId,
            foregroundThreadId,
            TRUE
        ) != FALSE;
    }

    if (targetThreadId != 0 &&
        targetThreadId != currentThreadId &&
        targetThreadId != foregroundThreadId)
    {
        attachedTarget = AttachThreadInput(
            currentThreadId,
            targetThreadId,
            TRUE
        ) != FALSE;
    }

    BringWindowToTop(topLevelWindow);
    SetForegroundWindow(topLevelWindow);
    SetActiveWindow(topLevelWindow);
    SetFocus(renderWindow);

    Sleep(25);

    if (attachedTarget)
        AttachThreadInput(currentThreadId, targetThreadId, FALSE);

    if (attachedForeground)
        AttachThreadInput(currentThreadId, foregroundThreadId, FALSE);

    if (!IsForegroundEmulator(topLevelWindow))
    {
        diagnostic =
            "Foreground activation failed for this LDPlayer instance. "
            "Mouse action cancelled rather than clicking another window.";
        return false;
    }

    diagnostic =
        "Focused LDPlayer HWND " +
        std::to_string(reinterpret_cast<uintptr_t>(topLevelWindow)) +
        ", render HWND " +
        std::to_string(reinterpret_cast<uintptr_t>(renderWindow)) + ".";

    return true;
}

bool GetScreenPointForEmulator(
    HWND renderWindow,
    int x,
    int y,
    POINT& screenPoint,
    std::string& diagnostic)
{
    RECT client{};
    if (!GetClientRect(renderWindow, &client))
    {
        diagnostic = "GetClientRect failed for LDPlayer render area.";
        return false;
    }

    const int width = client.right - client.left;
    const int height = client.bottom - client.top;

    if (width <= 0 || height <= 0)
    {
        diagnostic = "LDPlayer render area has invalid dimensions.";
        return false;
    }

    POINT origin{ 0, 0 };
    if (!ClientToScreen(renderWindow, &origin))
    {
        diagnostic = "ClientToScreen failed for LDPlayer render area.";
        return false;
    }

    // Use the center of the source pixel and keep the result inside the client.
    screenPoint.x = origin.x + static_cast<LONG>(
        (static_cast<long long>(2 * x + 1) * width) / (2 * SCREEN_WIDTH));
    screenPoint.y = origin.y + static_cast<LONG>(
        (static_cast<long long>(2 * y + 1) * height) / (2 * SCREEN_HEIGHT));

    return true;
}

bool IsPointOnEmulator(HWND topLevelWindow, HWND renderWindow, POINT point)
{
    const HWND hit = WindowFromPoint(point);
    return IsForegroundEmulator(topLevelWindow) && hit &&
        (hit == topLevelWindow || hit == renderWindow || IsChild(renderWindow, hit)) &&
        GetAncestor(hit, GA_ROOT) == topLevelWindow;
}

bool ClickEmulator(
    const std::string& deviceId,
    int x,
    int y,
    DWORD holdMs,
    bool legacyClick,
    std::string& diagnostic)
{
    if (x < 0 || x >= SCREEN_WIDTH || y < 0 || y >= SCREEN_HEIGHT)
    {
        diagnostic = "Invalid click coordinates.";
        return false;
    }

    HWND topLevelWindow = nullptr;
    HWND renderWindow = nullptr;
    if (!ActivateEmulatorWindow(deviceId, topLevelWindow, renderWindow, diagnostic))
        return false;

    POINT point{};
    if (!GetScreenPointForEmulator(renderWindow, x, y, point, diagnostic))
        return false;

    if (!IsPointOnEmulator(topLevelWindow, renderWindow, point))
    {
        diagnostic = "Click cancelled. The LDPlayer render area is covered or out of focus.";
        return false;
    }
    if (!SetCursorPos(point.x, point.y))
    {
        diagnostic = Win32Error("Cannot position cursor for click");
        return false;
    }

    if (holdMs > 28)
        Sleep(35);

    POINT current{};
    if (IsAutomationCancelled() || !GetCursorPos(&current) || current.x != point.x ||
        current.y != point.y || !IsPointOnEmulator(topLevelWindow, renderWindow, current))
    {
        diagnostic = "Click cancelled. The cursor or LDPlayer window changed before input.";
        return false;
    }

    if (legacyClick)
    {
        mouse_event(MOUSEEVENTF_LEFTDOWN, 0, 0, 0, 0);
        Sleep(holdMs);
        mouse_event(MOUSEEVENTF_LEFTUP, 0, 0, 0, 0);
    }
    else
    {
        INPUT button{};
        button.type = INPUT_MOUSE;
        button.mi.dwFlags = MOUSEEVENTF_LEFTDOWN;
        if (SendInput(1, &button, sizeof(INPUT)) != 1)
        {
            diagnostic = Win32Error("Cannot press left mouse button");
            return false;
        }

        Sleep(holdMs);

        button.mi.dwFlags = MOUSEEVENTF_LEFTUP;
        if (SendInput(1, &button, sizeof(INPUT)) != 1)
        {
            diagnostic = Win32Error("Cannot release left mouse button");
            mouse_event(MOUSEEVENTF_LEFTUP, 0, 0, 0, 0);
            return false;
        }
    }

    diagnostic = "Mouse click at game (" + std::to_string(x) + ", " + std::to_string(y) +
        "), desktop (" + std::to_string(point.x) + ", " + std::to_string(point.y) + ").";
    return true;
}

bool TapLoginButton(const std::string& deviceId, int x, int y, int attempt, std::string& diagnostic)
{
    return ClickEmulator(deviceId, x, y, attempt == 1 ? 85 : 95, attempt > 1, diagnostic);
}

bool TapADB(const std::string& deviceId, int x, int y, std::string& diagnostic)
{
    return ClickEmulator(deviceId, x, y, 28, false, diagnostic);
}

bool ConfirmKeyboardTarget(const std::string& deviceId, std::string& diagnostic)
{
    if (IsAutomationCancelled())
    {
        diagnostic = "Keyboard input cancelled.";
        return false;
    }

    const HWND window = GetMappedEmulatorWindow(deviceId);
    if (!IsForegroundEmulator(window))
    {
        diagnostic = "Keyboard input cancelled. The assigned LDPlayer window lost focus.";
        return false;
    }

    GUITHREADINFO info{};
    info.cbSize = sizeof(info);
    if (!GetGUIThreadInfo(0, &info) || !info.hwndFocus ||
        GetAncestor(info.hwndFocus, GA_ROOT) != window)
    {
        diagnostic = "Keyboard input cancelled. Focus is outside the assigned LDPlayer window.";
        return false;
    }
    return true;
}

bool SendKeyboardBatch(INPUT* events, UINT count, std::string& diagnostic)
{
    const UINT sent = SendInput(count, events, sizeof(INPUT));
    if (sent == count)
        return true;

    diagnostic = Win32Error("Cannot send keyboard input");
    for (UINT i = sent; i < count; ++i)
    {
        if (!(events[i].ki.dwFlags & KEYEVENTF_KEYUP))
            continue;

        for (UINT j = 0; j < sent; ++j)
        {
            if (events[j].ki.wVk == events[i].ki.wVk && events[j].ki.wScan == events[i].ki.wScan &&
                !(events[j].ki.dwFlags & KEYEVENTF_KEYUP))
            {
                SendInput(1, &events[i], sizeof(INPUT));
                break;
            }
        }
    }
    return false;
}

INPUT KeyEvent(WORD virtualKey, bool keyUp = false)
{
    INPUT event{};
    event.type = INPUT_KEYBOARD;
    event.ki.wVk = virtualKey;
    if (keyUp)
        event.ki.dwFlags = KEYEVENTF_KEYUP;
    return event;
}

bool SendHeldKey(WORD virtualKey, DWORD holdMs, std::string& diagnostic)
{
    INPUT down = KeyEvent(virtualKey);
    if (!SendKeyboardBatch(&down, 1, diagnostic))
        return false;

    Sleep(holdMs);

    INPUT up = KeyEvent(virtualKey, true);
    if (SendKeyboardBatch(&up, 1, diagnostic))
        return true;

    SendInput(1, &up, sizeof(INPUT));
    return false;
}

bool ClearADBTextField(
    const std::string& deviceId,
    int x,
    int y,
    std::string& diagnostic)
{
    if (!TapADB(deviceId, x, y, diagnostic))
        return false;

    Sleep(25);
    INPUT selectAll[] = { KeyEvent(VK_CONTROL), KeyEvent('A'), KeyEvent('A', true), KeyEvent(VK_CONTROL, true) };
    if (!ConfirmKeyboardTarget(deviceId, diagnostic) || !SendKeyboardBatch(selectAll, 4, diagnostic))
        return false;

    if (!ConfirmKeyboardTarget(deviceId, diagnostic) || !SendHeldKey(VK_BACK, 35, diagnostic))
        return false;

    Sleep(18);
    INPUT end[] = { KeyEvent(VK_END), KeyEvent(VK_END, true) };
    if (!ConfirmKeyboardTarget(deviceId, diagnostic) || !SendKeyboardBatch(end, 2, diagnostic))
        return false;

    // Some controls ignore Ctrl+A. Keep the existing fallback for short names.
    for (int i = 0; i < 24; ++i)
    {
        if (!ConfirmKeyboardTarget(deviceId, diagnostic) || !SendHeldKey(VK_BACK, 28, diagnostic))
            return false;
        Sleep(12);
    }

    diagnostic = "Cleared the focused name field.";
    return true;
}

// Generated names and configured passwords are restricted to ASCII letters/digits,
// which can be translated reliably into ordinary Windows keyboard scan codes.
bool IsSafeADBText(const std::string& value)
{
    if (value.empty())
        return false;

    for (unsigned char c : value)
    {
        const bool isLetter = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z');
        const bool isDigit = c >= '0' && c <= '9';
        if (!isLetter && !isDigit)
            return false;
    }

    return true;
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

    if (!ConfirmKeyboardTarget(deviceId, diagnostic))
        return false;

    const HKL layout = GetKeyboardLayout(GetWindowThreadProcessId(GetMappedEmulatorWindow(deviceId), nullptr));
    const std::wstring text = Utf8ToWide(value);

    // Validate the full string before pressing any key.
    std::vector<SHORT> mappings;
    mappings.reserve(text.size());
    for (wchar_t character : text)
    {
        const SHORT mapping = VkKeyScanExW(character, layout);
        if (mapping == -1 || (HIBYTE(mapping) & ~7) != 0)
        {
            diagnostic = "Switch the LDPlayer window to an English keyboard layout before starting automation.";
            return false;
        }
        mappings.push_back(mapping);
    }

    for (SHORT mapping : mappings)
    {
        if (!ConfirmKeyboardTarget(deviceId, diagnostic))
            return false;

        const WORD virtualKey = LOBYTE(mapping);
        const BYTE modifiers = HIBYTE(mapping);
        bool needShift = (modifiers & 1) != 0;
        const bool needControl = (modifiers & 2) != 0;
        const bool needAlt = (modifiers & 4) != 0;
        if (virtualKey >= 'A' && virtualKey <= 'Z' && (GetKeyState(VK_CAPITAL) & 1))
            needShift = !needShift;

        std::array<INPUT, 8> events{};
        UINT count = 0;
        const auto appendScanCode = [&](WORD key, bool keyUp)
        {
            const UINT scanCode = MapVirtualKeyExW(key, MAPVK_VK_TO_VSC_EX, layout);
            INPUT& event = events[count++];
            event.type = INPUT_KEYBOARD;
            event.ki.wScan = static_cast<WORD>(scanCode & 0xFF);
            event.ki.dwFlags = KEYEVENTF_SCANCODE;
            if ((scanCode & 0xFF00) == 0xE000)
                event.ki.dwFlags |= KEYEVENTF_EXTENDEDKEY;
            if (keyUp)
                event.ki.dwFlags |= KEYEVENTF_KEYUP;
        };

        if (needControl)
            appendScanCode(VK_CONTROL, false);
        if (needAlt)
            appendScanCode(VK_MENU, false);
        if (needShift)
            appendScanCode(VK_SHIFT, false);

        appendScanCode(virtualKey, false);
        appendScanCode(virtualKey, true);

        if (needShift)
            appendScanCode(VK_SHIFT, true);
        if (needAlt)
            appendScanCode(VK_MENU, true);
        if (needControl)
            appendScanCode(VK_CONTROL, true);

        for (UINT i = 0; i < count; ++i)
        {
            if (events[i].ki.wScan == 0)
            {
                diagnostic = "The LDPlayer keyboard layout has an unsupported scan code.";
                return false;
            }
        }

        if (!SendKeyboardBatch(events.data(), count, diagnostic))
            return false;

        if (!PauseAutomation(75))
        {
            diagnostic = "Keyboard input cancelled.";
            return false;
        }
    }

    diagnostic =
        "REAL WINDOWS KEYBOARD: sent " +
        std::to_string(text.size()) +
        " scan-code key presses through SendInput.";

    return true;
}

// ============================================================
// FILE PATHS
// ============================================================

std::wstring GetTemplatePath(const std::wstring& filename)
{
    std::wstring executable(32768, L'\0');
    const DWORD length = GetModuleFileNameW(
        nullptr, executable.data(), static_cast<DWORD>(executable.size()));
    if (!length || length >= executable.size())
        return {};

    executable.resize(length);
    const size_t separator = executable.find_last_of(L"\\/");
    if (separator == std::wstring::npos)
        return {};

    executable.resize(separator + 1);
    return executable + filename;
}

// ============================================================
// GENERATED NAMES FILE
// ============================================================

std::wstring GetNamesHistoryPath()
{
    wchar_t desktop[MAX_PATH]{};
    if (FAILED(SHGetFolderPathW(nullptr, CSIDL_DESKTOPDIRECTORY, nullptr, SHGFP_TYPE_CURRENT, desktop)))
        return {};

    return std::wstring(desktop) + L"\\SmartClick_Names.txt";
}

bool SaveGeneratedName(
    const std::string& firstName,
    const std::string& lastName,
    std::string& diagnostic)
{
    const std::wstring filePath = GetNamesHistoryPath();
    if (filePath.empty())
    {
        diagnostic = "Cannot get Windows Desktop path.";
        return false;
    }

    const std::string line = "login - \"" + firstName + "_" + lastName + "\"\r\n";

    std::lock_guard<std::mutex> lock(g_NamesFileMutex);

    const UniqueHandle file(CreateFileW(
        filePath.c_str(),
        FILE_APPEND_DATA,
        FILE_SHARE_READ,
        nullptr,
        OPEN_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        nullptr
    ));

    if (file.get() == INVALID_HANDLE_VALUE)
    {
        diagnostic = "Cannot create or open SmartClick_Names.txt.";
        return false;
    }

    DWORD bytesWritten = 0;

    BOOL written = WriteFile(
        file.get(),
        line.data(),
        static_cast<DWORD>(line.size()),
        &bytesWritten,
        nullptr
    );

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

    const UniqueHandle file(CreateFileW(
        path.c_str(),
        GENERIC_READ,
        FILE_SHARE_READ,
        nullptr,
        OPEN_EXISTING,
        FILE_ATTRIBUTE_NORMAL,
        nullptr
    ));

    if (file.get() == INVALID_HANDLE_VALUE)
    {
        diagnostic =
            "Cannot open file: " +
            WideToUtf8(path);

        return false;
    }

    LARGE_INTEGER fileSize{};

    if (!GetFileSizeEx(file.get(), &fileSize) ||
        fileSize.QuadPart <= 0 ||
        fileSize.QuadPart > 100 * 1024 * 1024)
    {
        diagnostic = "Invalid template file size.";
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
            file.get(),
            data.data() + totalRead,
            requested,
            &bytesRead,
            nullptr) || bytesRead == 0)
        {
            diagnostic = "Cannot read complete file.";
            data.clear();
            return false;
        }

        totalRead += bytesRead;
    }

    return true;
}

// ============================================================
// TEMPLATE LOADING
// ============================================================

bool TemplateHasContrast(const cv::Mat& image)
{
    cv::Scalar mean;
    cv::Scalar deviation;
    cv::meanStdDev(image, mean, deviation);
    return deviation[0] > 0.0 || deviation[1] > 0.0 || deviation[2] > 0.0;
}

bool LoadPhotonTemplate(
    const std::wstring& path,
    cv::Mat& destination,
    std::string& diagnostic)
{
    destination.release();
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

        if (!TemplateHasContrast(decoded))
        {
            diagnostic = "Template has no contrast: " + WideToUtf8(path);
            return false;
        }

        destination = std::move(decoded);

        diagnostic =
            "Loaded " + WideToUtf8(path) +
            " (" +
            std::to_string(destination.cols) + "x" +
            std::to_string(destination.rows) + ")";

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

    LoadPhotonTemplate(
        GetTemplatePath(L"photon_after_login.png"),
        g_PhotonAfterLoginTemplate,
        diagnostic
    );

    status << "photon_after_login.png (optional): " << diagnostic << "\n";

    g_StageTemplates.clear();

    bool allStageTemplates = true;

    for (const std::string& name : g_RegistrationTemplates)
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

    g_TemplatesLoaded = ready;

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
    for (const std::string& name : g_RegistrationTemplates)
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

bool DecodeImage(
    const std::vector<unsigned char>& data,
    cv::Mat& image,
    std::string& diagnostic,
    cv::Size* originalSize)
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

        if (originalSize)
            *originalSize = image.size();

        if (image.cols != SCREEN_WIDTH ||
            image.rows != SCREEN_HEIGHT)
        {
            const bool supported = image.cols >= 320 &&
                static_cast<long long>(image.cols) * SCREEN_HEIGHT ==
                static_cast<long long>(image.rows) * SCREEN_WIDTH;
            if (!supported)
            {
                diagnostic = "Expected a landscape 16:9 screenshot, got " +
                    std::to_string(image.cols) + "x" + std::to_string(image.rows) + ".";
                image.release();
                return false;
            }

            const int interpolation = image.cols > SCREEN_WIDTH ? cv::INTER_AREA : cv::INTER_LINEAR;
            cv::resize(image, image, cv::Size(SCREEN_WIDTH, SCREEN_HEIGHT), 0.0, 0.0, interpolation);
        }

        return true;
    }
    catch (const cv::Exception& e)
    {
        diagnostic = e.what();
        return false;
    }
}

bool CaptureADBScreenshot(
    const std::string& deviceId,
    cv::Mat& screen,
    std::string& diagnostic,
    ULONGLONG deadline,
    cv::Size* originalSize = nullptr)
{
    constexpr DWORD maxCaptureMs = 4000;
    const DWORD timeout = std::min(maxCaptureMs, RemainingTime(deadline));
    if (!timeout)
    {
        diagnostic = "Screenshot deadline expired.";
        return false;
    }

    std::vector<unsigned char> imageData;
    const std::wstring arguments = L"-s " + DeviceArgument(deviceId) + L" exec-out screencap -p";
    return RunProcess(ADBExecutable(), arguments, imageData, diagnostic, timeout, false, true) &&
        DecodeImage(imageData, screen, diagnostic, originalSize);
}

// ============================================================
// IMAGE RECOGNITION
// ============================================================

bool DetectPhotonTemplate(
    const std::string& deviceId,
    const cv::Mat& templateImage,
    double& confidence,
    POINT& matchCenter,
    std::string& diagnostic,
    ULONGLONG deadline)
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
        cv::Mat screenshot;
        if (!CaptureADBScreenshot(deviceId, screenshot, diagnostic, deadline))
            return false;

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
        deviceId, g_PhotonReadyTemplate, confidence, center, diagnostic,
        GetTickCount64() + LOGIN_TIMEOUT_MS);
}

// Field placeholders can vary slightly due to WebView rendering.
// Match in grayscale at several nearby scales and use a dedicated threshold.
bool DetectInputField(
    const std::string& deviceId,
    const std::string& templateName,
    double& confidence,
    POINT& center,
    std::string& diagnostic,
    ULONGLONG deadline)
{
    confidence = 0.0;
    center = { 0, 0 };

    auto it = g_StageTemplates.find(templateName);
    if (it == g_StageTemplates.end() || it->second.empty())
    {
        diagnostic = "Input-field template missing: " + templateName + ".png";
        return false;
    }

    cv::Mat screenshot;
    if (!CaptureADBScreenshot(deviceId, screenshot, diagnostic, deadline))
        return false;

    try
    {
        cv::Mat screenGray;
        cv::cvtColor(screenshot, screenGray, cv::COLOR_BGR2GRAY);

        cv::Mat templateGray;
        cv::cvtColor(it->second, templateGray, cv::COLOR_BGR2GRAY);

        const double scales[] = { 0.95, 1.0, 1.05 };
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

            if (!TemplateHasContrast(scaledTemplate))
                continue;

            // Restrict the search to candidates with centers inside the form.
            const int left = std::max(0, 60 - width / 2);
            const int top = std::max(0, 160 - height / 2);
            const int right = std::min(screenGray.cols, 420 - width / 2 + width);
            const int bottom = std::min(screenGray.rows, 420 - height / 2 + height);
            if (right - left < width || bottom - top < height)
                continue;

            const cv::Rect searchArea(left, top, right - left, bottom - top);
            cv::Mat matchResult;
            cv::matchTemplate(screenGray(searchArea), scaledTemplate, matchResult, cv::TM_CCOEFF_NORMED);

            double maxValue = 0.0;
            cv::Point maxLocation;
            cv::minMaxLoc(matchResult, nullptr, &maxValue, nullptr, &maxLocation);

            if (std::isfinite(maxValue) && maxValue > bestScore)
            {
                bestScore = maxValue;
                bestLocation = maxLocation + searchArea.tl();
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

        return confidence >= 0.52;
    }
    catch (const cv::Exception& e)
    {
        diagnostic = std::string("OpenCV field matching error: ") + e.what();
        return false;
    }
}

bool MatchesAreStable(POINT previous, POINT current)
{
    constexpr LONG maxMovement = 12;
    return std::abs(previous.x - current.x) <= maxMovement &&
        std::abs(previous.y - current.y) <= maxMovement;
}

bool WaitForInputField(
    const std::string& deviceId,
    const std::string& templateName,
    POINT& center,
    std::string& diagnostic,
    int timeoutMs)
{
    const ULONGLONG deadline = GetTickCount64() + timeoutMs;
    constexpr size_t previousFrameCount = 4;
    std::array<POINT, previousFrameCount> previousCenters{};
    std::array<bool, previousFrameCount> previousMatches{};
    size_t nextIndex = 0;
    double bestConfidence = -1.0;
    std::string bestDiagnostic;
    std::string lastDiagnostic;

    while (!IsAutomationCancelled() && RemainingTime(deadline))
    {
        POINT currentCenter{};
        double confidence = 0.0;
        const bool found = DetectInputField(
            deviceId, templateName, confidence, currentCenter, lastDiagnostic, deadline);

        if (found && !IsAutomationCancelled() && RemainingTime(deadline))
        {
            for (size_t index = 0; index < previousFrameCount; ++index)
            {
                if (previousMatches[index] && MatchesAreStable(previousCenters[index], currentCenter))
                {
                    center = currentCenter;
                    diagnostic = "Input field confirmed in two of the last five frames. " + lastDiagnostic;
                    return true;
                }
            }

            if (confidence > bestConfidence)
            {
                bestConfidence = confidence;
                bestDiagnostic = lastDiagnostic;
            }
        }

        previousMatches[nextIndex] = found;
        previousCenters[nextIndex] = currentCenter;
        nextIndex = (nextIndex + 1) % previousFrameCount;
        PauseAutomation(std::min<DWORD>(100, RemainingTime(deadline)));
    }

    if (IsAutomationCancelled())
        diagnostic = "Cancelled while waiting for " + templateName + ".png.";
    else
        diagnostic = "Timeout waiting for " + templateName + ".png. Last frame: " + lastDiagnostic +
            (bestDiagnostic.empty() ? "" : " Best field match: " + bestDiagnostic);
    return false;
}

template <typename Detect>
bool WaitForTemplate(
    const std::string& name,
    int timeoutMs,
    int requiredMatches,
    Detect detect,
    double& confidence,
    POINT& center,
    std::string& diagnostic)
{
    const ULONGLONG deadline = GetTickCount64() + timeoutMs;
    POINT previousCenter{};
    int consecutive = 0;
    std::string lastDiagnostic;
    confidence = 0.0;
    center = {};

    while (!IsAutomationCancelled() && RemainingTime(deadline))
    {
        POINT currentCenter{};
        const bool found = detect(confidence, currentCenter, lastDiagnostic, deadline);
        if (found && !IsAutomationCancelled() && RemainingTime(deadline))
        {
            consecutive = consecutive > 0 && MatchesAreStable(previousCenter, currentCenter)
                ? consecutive + 1 : 1;
            previousCenter = currentCenter;
            if (consecutive == requiredMatches)
            {
                center = currentCenter;
                diagnostic = name + " confirmed. " + lastDiagnostic;
                return true;
            }
        }
        else
        {
            consecutive = 0;
        }

        PauseAutomation(std::min<DWORD>(DETECTION_INTERVAL_MS, RemainingTime(deadline)));
    }

    if (IsAutomationCancelled())
        diagnostic = "Cancelled while waiting for " + name + ".";
    else
        diagnostic = "Timeout waiting for " + name + " after " +
            std::to_string(timeoutMs / 1000) + " seconds. Last result: " + lastDiagnostic;
    return false;
}

bool WaitForPhotonReady(
    const std::string& deviceId,
    double& confidence,
    POINT& center,
    std::string& diagnostic,
    int timeoutMs)
{
    return WaitForTemplate("Login screen", timeoutMs, 1,
        [&](double& score, POINT& point, std::string& last, ULONGLONG deadline)
        {
            return DetectPhotonTemplate(deviceId, g_PhotonReadyTemplate, score, point, last, deadline);
        },
        confidence, center, diagnostic);
}

bool WaitForPhotonAfterLogin(
    const std::string& deviceId,
    double& confidence,
    std::string& diagnostic,
    int timeoutMs)
{
    if (g_PhotonAfterLoginTemplate.empty())
    {
        diagnostic = "Optional photon_after_login.png is unavailable.";
        return false;
    }

    POINT center{};
    return WaitForTemplate("After-login screen", timeoutMs, 1,
        [&](double& score, POINT& point, std::string& last, ULONGLONG deadline)
        {
            return DetectPhotonTemplate(deviceId, g_PhotonAfterLoginTemplate, score, point, last, deadline);
        },
        confidence, center, diagnostic);
}

bool WaitForStage(
    const std::string& deviceId,
    const std::string& templateName,
    POINT& center,
    std::string& diagnostic,
    int timeoutMs = STAGE_TIMEOUT_MS)
{
    const auto stage = g_StageTemplates.find(templateName);
    if (stage == g_StageTemplates.end())
    {
        diagnostic = "Template not loaded: " + templateName + ".png.";
        return false;
    }

    double confidence = 0.0;
    return WaitForTemplate(templateName + ".png", timeoutMs, 2,
        [&](double& score, POINT& point, std::string& last, ULONGLONG deadline)
        {
            return DetectPhotonTemplate(deviceId, stage->second, score, point, last, deadline);
        },
        confidence, center, diagnostic);
}

bool WaitAndTapStage(
    const std::string& deviceId,
    const std::string& templateName,
    std::ostream& log)
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
// PHOTON MARKER DETECTION
// The marker is rendered at a slightly different scale between emulator
// captures. Search only the upper-left UI area, use multi-scale grayscale
// matching, then verify that the candidate patch actually contains purple.
// ============================================================

bool DetectPhotonMarkerTemplate(
    const std::string& deviceId,
    const cv::Mat& templateImage,
    double& confidence,
    POINT& matchCenter,
    std::string& diagnostic,
    ULONGLONG deadline,
    cv::Size& originalSize)
{
    confidence = 0.0;
    matchCenter = { 0, 0 };

    if (templateImage.empty())
    {
        diagnostic = "PHOTON marker template is empty.";
        return false;
    }

    cv::Mat screenshot;
    if (!CaptureADBScreenshot(deviceId, screenshot, diagnostic, deadline, &originalSize))
        return false;

    try
    {
        const cv::Rect searchArea(
            0,
            0,
            std::min(360, screenshot.cols),
            std::min(300, screenshot.rows));

        if (searchArea.width < 16 || searchArea.height < 16)
        {
            diagnostic = "PHOTON marker search area is too small.";
            return false;
        }

        cv::Mat screenRoi = screenshot(searchArea);
        cv::Mat screenGray;
        cv::cvtColor(screenRoi, screenGray, cv::COLOR_BGR2GRAY);

        cv::Mat templateGray;
        cv::cvtColor(templateImage, templateGray, cv::COLOR_BGR2GRAY);

        cv::Mat hsv;
        cv::cvtColor(screenRoi, hsv, cv::COLOR_BGR2HSV);
        cv::Mat purpleMask;
        cv::inRange(hsv, cv::Scalar(112, 55, 35), cv::Scalar(175, 255, 255), purpleMask);
        cv::Mat purpleIntegral;
        cv::integral(purpleMask, purpleIntegral, CV_32S);

        const double scales[] =
        {
            0.55, 0.65, 0.75, 0.85, 0.95,
            1.00, 1.10, 1.20, 1.30, 1.45, 1.60
        };

        double bestScore = -1.0;
        double bestPurpleRatio = 0.0;
        cv::Point bestLocation{};
        cv::Size bestSize{};

        for (double scale : scales)
        {
            const int width = static_cast<int>(
                std::round(templateGray.cols * scale));
            const int height = static_cast<int>(
                std::round(templateGray.rows * scale));

            if (width < 12 || height < 12 ||
                width > screenGray.cols || height > screenGray.rows)
                continue;

            cv::Mat scaledTemplate;
            cv::resize(
                templateGray,
                scaledTemplate,
                cv::Size(width, height),
                0.0,
                0.0,
                scale < 1.0 ? cv::INTER_AREA : cv::INTER_CUBIC);

            if (!TemplateHasContrast(scaledTemplate))
                continue;

            cv::Mat validPositions(screenGray.rows - height + 1, screenGray.cols - width + 1, CV_8U);
            const int minPurpleSum = static_cast<int>(std::ceil(0.035 * width * height * 255));
            for (int y = 0; y < validPositions.rows; ++y)
            {
                const int* top = purpleIntegral.ptr<int>(y);
                const int* bottom = purpleIntegral.ptr<int>(y + height);
                unsigned char* valid = validPositions.ptr<unsigned char>(y);
                for (int x = 0; x < validPositions.cols; ++x)
                    valid[x] = bottom[x + width] - top[x + width] - bottom[x] + top[x] >= minPurpleSum;
            }
            if (!cv::countNonZero(validPositions))
                continue;

            cv::Mat matchResult;
            cv::matchTemplate(screenGray, scaledTemplate, matchResult, cv::TM_CCOEFF_NORMED);

            double maxValue = 0.0;
            cv::Point maxLocation;
            cv::minMaxLoc(matchResult, nullptr, &maxValue, nullptr, &maxLocation, validPositions);

            if (std::isfinite(maxValue) && maxValue > bestScore)
            {
                bestScore = maxValue;
                bestLocation = maxLocation;
                bestSize = cv::Size(width, height);
                const int x = maxLocation.x;
                const int y = maxLocation.y;
                const int* top = purpleIntegral.ptr<int>(y);
                const int* bottom = purpleIntegral.ptr<int>(y + height);
                bestPurpleRatio = (bottom[x + width] - top[x + width] - bottom[x] + top[x]) /
                    (255.0 * width * height);
            }
        }

        if (bestScore < 0.0)
        {
            diagnostic = "PHOTON marker: no valid match containing purple.";
            return false;
        }

        confidence = bestScore;
        matchCenter.x =
            searchArea.x + bestLocation.x + bestSize.width / 2;
        matchCenter.y =
            searchArea.y + bestLocation.y + bestSize.height / 2;

        diagnostic =
            "PHOTON marker multi-scale match: " +
            std::to_string(bestScore * 100.0) +
            "%, purple pixels: " +
            std::to_string(bestPurpleRatio * 100.0) +
            "%, center: (" +
            std::to_string(matchCenter.x) + ", " +
            std::to_string(matchCenter.y) + ").";

        return bestScore >= 0.60;
    }
    catch (const cv::Exception& e)
    {
        diagnostic = std::string("PHOTON marker OpenCV error: ") + e.what();
        return false;
    }
    catch (const std::exception& e)
    {
        diagnostic = std::string("PHOTON marker error: ") + e.what();
        return false;
    }
}

// ============================================================
// POST-AUTOMATION IMAGE SEQUENCE
// ============================================================

bool LoadExternalTemplate(
    const std::string& stem,
    cv::Mat& image,
    std::ostream& log)
{
    constexpr std::array<const char*, 3> extensions{ ".png", ".jpg", ".jpeg" };
    for (const char* extension : extensions)
    {
        const std::string filename = stem + extension;
        std::string diagnostic;
        if (LoadPhotonTemplate(GetTemplatePath(Utf8ToWide(filename)), image, diagnostic))
        {
            log << diagnostic << "\n";
            return true;
        }
        log << "Cannot load " << filename << ". " << diagnostic << "\n";
    }
    return false;
}

bool TapPhotonMarker(
    const std::string& deviceId,
    POINT center,
    cv::Size originalSize,
    std::string& diagnostic)
{
    if (originalSize.width <= 0 || originalSize.height <= 0 ||
        center.x < 0 || center.x >= SCREEN_WIDTH || center.y < 0 || center.y >= SCREEN_HEIGHT)
    {
        diagnostic = "Invalid PHOTON marker touch coordinates.";
        return false;
    }

    const auto x = (2LL * center.x + 1) * originalSize.width / (2 * SCREEN_WIDTH);
    const auto y = (2LL * center.y + 1) * originalSize.height / (2 * SCREEN_HEIGHT);
    const std::wstring arguments = L"-s " + DeviceArgument(deviceId) +
        L" shell input touchscreen tap " + std::to_wstring(x) + L" " + std::to_wstring(y);

    std::vector<unsigned char> output;
    const bool succeeded = RunProcess(ADBExecutable(), arguments, output, diagnostic, 5000, true, true);
    const std::string response = Trim(std::string(output.begin(), output.end()));
    // Android's input command may print an error even when the shell returns zero.
    if (!succeeded || !response.empty())
    {
        if (!response.empty())
        {
            if (!diagnostic.empty())
                diagnostic += " ";
            diagnostic += response;
        }
        return false;
    }

    diagnostic = "ADB touchscreen tap sent for PHOTON marker at (" + std::to_string(x) +
        ", " + std::to_string(y) + ").";
    return true;
}

bool RunPostAutomationImageSequence(
    const std::string& deviceId,
    std::ostream& log)
{
    log << "\nPOST-AUTOMATION IMAGE SEQUENCE\n";

    constexpr std::array<const char*, 7> names
    {
        "photon_marker", "target_1", "target_2", "target_3", "target_4", "target_5", "target_6"
    };
    std::array<cv::Mat, names.size()> templates;
    for (size_t i = 0; i < names.size(); ++i)
    {
        if (IsAutomationCancelled() || !LoadExternalTemplate(names[i], templates[i], log))
            return false;
    }

    double score = 0.0;
    POINT center{};
    std::string diagnostic;
    cv::Size originalSize;
    const auto detectMarker = [&](double& confidence, POINT& point, std::string& last, ULONGLONG deadline)
    {
        return DetectPhotonMarkerTemplate(deviceId, templates[0], confidence, point, last, deadline, originalSize);
    };
    log << "Waiting for photon_marker\n";
    if (!WaitForTemplate(names[0], STAGE_TIMEOUT_MS, 2, detectMarker, score, center, diagnostic))
    {
        log << diagnostic << "\n";
        return false;
    }
    log << diagnostic << "\n";
    const POINT tappedCenter = center;
    const bool pressed = ClickEmulator(deviceId, center.x, center.y, 160, false, diagnostic);
    log << (pressed ? "Marker mouse press (160 ms). " : "Marker mouse press failed. ") << diagnostic << "\n";

    for (size_t i = 1; i < names.size(); ++i)
    {
        log << "Waiting for " << names[i] << "\n";
        std::string lastImageMatch;
        const auto detectTarget = [&](double& confidence, POINT& point, std::string& last, ULONGLONG deadline)
        {
            const bool found = DetectPhotonTemplate(deviceId, templates[i], confidence, point, last, deadline);
            if (last.rfind("Match: ", 0) == 0)
                lastImageMatch = last;
            return found;
        };
        bool found = WaitForTemplate(names[i], i == 1 ? 6000 : STAGE_TIMEOUT_MS,
            2, detectTarget, score, center, diagnostic);
        if (i == 1 && !found && !IsAutomationCancelled())
        {
            log << diagnostic << "\n";
            POINT markerCenter{};
            std::string markerDiagnostic;
            if (WaitForTemplate(names[0], 4500, 2, detectMarker, score, markerCenter, markerDiagnostic) &&
                MatchesAreStable(tappedCenter, markerCenter))
            {
                // Check for a late transition before pressing the marker a second time.
                found = detectTarget(score, center, diagnostic, GetTickCount64() + 4000);
                if (found)
                    found = WaitForTemplate(names[i], 4500, 2, detectTarget, score, center, diagnostic);
                else if (diagnostic.rfind("Match: ", 0) == 0 && !IsAutomationCancelled())
                {
                    log << "Marker still visible. Trying an ADB touchscreen tap.\n";
                    const bool tapSent = TapPhotonMarker(deviceId, markerCenter, originalSize, diagnostic);
                    log << (tapSent ? "" : "ADB marker tap failed. ") << diagnostic << "\n";
                }
            }
            else
            {
                log << "Original marker position no longer confirmed. " << markerDiagnostic << "\n";
            }
            if (!found)
                found = WaitForTemplate(names[i], STAGE_TIMEOUT_MS, 2, detectTarget, score, center, diagnostic);
        }

        if (!found)
        {
            log << diagnostic << "\n";
            if (!lastImageMatch.empty())
                log << "Last image comparison: " << lastImageMatch << "\n";
            return false;
        }

        log << diagnostic << "\n";
        if (!TapADB(deviceId, center.x, center.y, diagnostic))
        {
            log << "Click failed. " << diagnostic << "\n";
            return false;
        }
        log << diagnostic << "\n";
        if (!PauseAutomation(250))
            return false;
    }

    log << "POST-AUTOMATION IMAGE SEQUENCE COMPLETED.\n";
    return true;
}

// ============================================================
// RANDOM ROLEPLAY NAMES
// ============================================================

// Load all previously generated logins from the Desktop history file.
// This makes uniqueness persistent between SmartClick launches.
bool LoadUsedRoleplayNames(
    std::unordered_set<std::string>& usedFullNames,
    std::unordered_set<std::string>& usedFirstNames,
    std::unordered_set<std::string>& usedLastNames,
    std::string& diagnostic)
{
    const std::wstring filePath = GetNamesHistoryPath();
    if (filePath.empty())
    {
        diagnostic = "Cannot locate Windows Desktop for unique-name history.";
        return false;
    }

    const UniqueHandle file(CreateFileW(
        filePath.c_str(),
        GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_WRITE,
        nullptr,
        OPEN_EXISTING,
        FILE_ATTRIBUTE_NORMAL,
        nullptr
    ));

    if (file.get() == INVALID_HANDLE_VALUE)
    {
        if (GetLastError() == ERROR_FILE_NOT_FOUND ||
            GetLastError() == ERROR_PATH_NOT_FOUND)
        {
            diagnostic = "No previous name history; starting a new unique-name list.";
            return true;
        }

        diagnostic =
            "Cannot read SmartClick_Names.txt. Win32 error: " +
            std::to_string(GetLastError());
        return false;
    }

    LARGE_INTEGER fileSize{};
    if (!GetFileSizeEx(file.get(), &fileSize) ||
        fileSize.QuadPart < 0 ||
        fileSize.QuadPart > 20 * 1024 * 1024)
    {
        diagnostic = "Name history file size is invalid.";
        return false;
    }

    std::string contents(static_cast<size_t>(fileSize.QuadPart), '\0');
    size_t totalRead = 0;

    while (totalRead < contents.size())
    {
        DWORD bytesRead = 0;
        const DWORD request = static_cast<DWORD>(
            std::min<size_t>(contents.size() - totalRead, 1024 * 1024)
        );

        if (!ReadFile(
            file.get(),
            contents.data() + totalRead,
            request,
            &bytesRead,
            nullptr) || bytesRead == 0)
        {
            diagnostic = "Cannot read complete SmartClick_Names.txt.";
            return false;
        }

        totalRead += bytesRead;
    }

    auto normalize = [](std::string value)
    {
        std::transform(
            value.begin(),
            value.end(),
            value.begin(),
            [](unsigned char ch)
            {
                return static_cast<char>(std::tolower(ch));
            }
        );
        return value;
    };

    std::istringstream lines(contents);
    std::string line;

    while (std::getline(lines, line))
    {
        const size_t prefix = line.find("login - \"");
        if (prefix == std::string::npos)
            continue;

        const size_t valueStart = prefix + 9;
        const size_t valueEnd = line.find('"', valueStart);

        if (valueEnd == std::string::npos)
            continue;

        const std::string login =
            line.substr(valueStart, valueEnd - valueStart);

        const size_t separator = login.find('_');
        if (separator == std::string::npos)
            continue;

        const std::string firstName =
            normalize(login.substr(0, separator));
        const std::string lastName =
            normalize(login.substr(separator + 1));

        if (firstName.empty() || lastName.empty())
            continue;

        usedFullNames.insert(firstName + "_" + lastName);
        usedFirstNames.insert(firstName);
        usedLastNames.insert(lastName);
    }

    diagnostic =
        "Loaded " + std::to_string(usedFullNames.size()) +
        " previously used full names.";

    return true;
}

std::pair<std::string, std::string> GenerateRoleplayName(
    const std::string& deviceId)
{
    static const std::vector<std::string> firstNames =
    {
        "James", "John", "Robert", "Michael", "William", "David",
        "Richard", "Joseph", "Thomas", "Charles", "Christopher", "Daniel",
        "Matthew", "Anthony", "Mark", "Donald", "Steven", "Paul",
        "Andrew", "Joshua", "Kenneth", "Kevin", "Brian", "George",
        "Timothy", "Ronald", "Edward", "Jason", "Jeffrey", "Ryan",
        "Jacob", "Gary", "Nicholas", "Eric", "Jonathan", "Stephen",
        "Larry", "Justin", "Scott", "Brandon", "Benjamin", "Samuel",
        "Gregory", "Alexander", "Patrick", "Frank", "Raymond", "Jack",
        "Dennis", "Jerry", "Tyler", "Aaron", "Adam", "Nathan",
        "Henry", "Zachary", "Douglas", "Peter", "Kyle", "Walter",
        "Ethan", "Jeremy", "Keith", "Christian", "Roger", "Noah",
        "Gerald", "Carl", "Sean", "Austin", "Arthur", "Lawrence",
        "Jesse", "Dylan", "Bryan", "Jordan", "Bruce", "Albert",
        "Gabriel", "Logan", "Alan", "Wayne", "Vincent", "Russell",
        "Elijah", "Louis", "Philip", "Bradley", "Cameron", "Connor",
        "Evan", "Hunter", "Liam", "Mason", "Caleb", "Owen",
        "Wyatt", "Luke", "Isaac", "Julian", "Grayson", "Levi",
        "Aiden", "Miles", "Eli", "Theo", "Nolan", "Colton",
        "Emma", "Olivia", "Ava", "Sophia", "Isabella", "Mia",
        "Charlotte", "Amelia", "Harper", "Evelyn", "Abigail", "Emily",
        "Elizabeth", "Sofia", "Avery", "Ella", "Scarlett", "Grace",
        "Chloe", "Victoria", "Riley", "Aria", "Lily", "Zoey",
        "Nora", "Hannah", "Layla", "Addison", "Ellie", "Stella",
        "Natalie", "Claire", "Audrey", "Brooklyn", "Savannah", "Lucy"
    };

    static const std::vector<std::string> lastNames =
    {
        "Smith", "Johnson", "Williams", "Brown", "Jones", "Garcia",
        "Miller", "Davis", "Rodriguez", "Martinez", "Hernandez", "Lopez",
        "Gonzalez", "Wilson", "Anderson", "Thomas", "Taylor", "Moore",
        "Jackson", "Martin", "Lee", "Perez", "Thompson", "White",
        "Harris", "Sanchez", "Clark", "Ramirez", "Lewis", "Robinson",
        "Walker", "Young", "Allen", "King", "Wright", "Scott",
        "Torres", "Nguyen", "Hill", "Flores", "Green", "Adams",
        "Nelson", "Baker", "Hall", "Rivera", "Campbell", "Mitchell",
        "Carter", "Roberts", "Gomez", "Phillips", "Evans", "Turner",
        "Diaz", "Parker", "Cruz", "Edwards", "Collins", "Reyes",
        "Stewart", "Morris", "Morales", "Murphy", "Cook", "Rogers",
        "Gutierrez", "Ortiz", "Morgan", "Cooper", "Peterson", "Bailey",
        "Reed", "Kelly", "Howard", "Ramos", "Kim", "Cox",
        "Ward", "Richardson", "Watson", "Brooks", "Chavez", "Wood",
        "Bennett", "Gray", "Mendoza", "Ruiz", "Hughes", "Price",
        "Alvarez", "Castillo", "Sanders", "Myers", "Long", "Ross",
        "Foster", "Jimenez", "Powell", "Jenkins", "Perry", "Russell",
        "Sullivan", "Bell", "Coleman", "Butler", "Henderson", "Barnes",
        "Fisher", "Simmons", "Patterson", "Alexander", "Hamilton", "Graham",
        "Reynolds", "Griffin", "Wallace", "West", "Cole", "Hayes",
        "Bryant", "Herrera", "Gibson", "Ellis", "Tran", "Medina",
        "Aguilar", "Stevens", "Murray", "Ford", "Castro", "Marshall"
    };

    // Remove accidental duplicate entries from source lists before constructing
    // combinations. This ensures each generated first/surname value is weighted once.
    auto normalizeName = [](std::string value)
    {
        std::transform(
            value.begin(),
            value.end(),
            value.begin(),
            [](unsigned char ch)
            {
                return static_cast<char>(std::tolower(ch));
            }
        );
        return value;
    };

    std::vector<std::string> uniqueFirstNames;
    std::vector<std::string> uniqueLastNames;
    std::unordered_set<std::string> seenFirstNames;
    std::unordered_set<std::string> seenLastNames;

    for (const std::string& name : firstNames)
    {
        if (seenFirstNames.insert(normalizeName(name)).second)
            uniqueFirstNames.push_back(name);
    }

    for (const std::string& name : lastNames)
    {
        if (seenLastNames.insert(normalizeName(name)).second)
            uniqueLastNames.push_back(name);
    }

    // Read a consistent snapshot of the name history.
    std::lock_guard<std::mutex> historyLock(g_NamesFileMutex);

    std::unordered_set<std::string> usedFullNames;
    std::unordered_set<std::string> usedFirstNames;
    std::unordered_set<std::string> usedLastNames;
    std::string historyDiagnostic;

    if (!LoadUsedRoleplayNames(
        usedFullNames,
        usedFirstNames,
        usedLastNames,
        historyDiagnostic))
    {
        return {};
    }

    std::random_device randomDevice;
    const auto timeSeed =
        static_cast<unsigned long long>(
            std::chrono::high_resolution_clock::now()
                .time_since_epoch().count()
        );

    std::seed_seq seed
    {
        randomDevice(), randomDevice(), randomDevice(), randomDevice(),
        static_cast<unsigned int>(GetTickCount64()),
        static_cast<unsigned int>(timeSeed),
        static_cast<unsigned int>(timeSeed >> 32),
        static_cast<unsigned int>(
            std::hash<std::string>{}(deviceId))
    };

    std::mt19937_64 generator(seed);

    // Add pronounceable fictional American-style names. These are generated
    // from random syllable combinations and filtered against the saved history.
    const std::vector<std::string> firstStarts =
    {
        "Aver", "Bray", "Cal", "Cor", "Daven", "Eli", "Fay",
        "Garr", "Harlan", "Jor", "Kellan", "Lenn", "Mav", "Norr",
        "Orin", "Perr", "Quin", "Renn", "Soren", "Tav", "Vey",
        "Wyn", "Zay", "Bex", "Cade", "Dax", "Evren", "Fenn",
        "Jalen", "Kael", "Lior", "Merr", "Nyle", "Orren", "Rylan",
        "Taren", "Varen", "Wells", "Zev"
    };

    const std::vector<std::string> firstEnds =
    {
        "den", "ley", "ton", "son", "win", "len", "rick",
        "vin", "lan", "mon", "ran", "ford", "las", "ian",
        "ett", "an", "el", "is", "en", "er", "ar", "on",
        "ric", "well", "wyn", "ley", "bert", "lin", "ric",
        "more", "den", "ley", "wyn", "ace", "ory", "ett"
    };

    const std::vector<std::string> surnameStarts =
    {
        "Ash", "Black", "Brook", "Cald", "Cedar", "Clear", "Dun",
        "Ever", "Fair", "Fox", "Grey", "Hart", "Hollow", "Kings",
        "Lake", "Marl", "North", "Oak", "Pine", "Raven", "Silver",
        "Stone", "West", "White", "Willow", "Winter", "Wood",
        "Amber", "Arden", "Briar", "Crest", "Dover", "Elm",
        "Glen", "Haven", "Iron", "Laurel", "Meadow", "Ridge"
    };

    const std::vector<std::string> surnameEnds =
    {
        "brook", "field", "ford", "gate", "ham", "hill", "land",
        "ley", "more", "ridge", "stone", "vale", "well", "wood",
        "worth", "man", "ton", "son", "er", "by", "croft",
        "haven", "hurst", "mont", "wick", "shaw", "dale", "burn"
    };

    std::uniform_int_distribution<size_t> firstStartPick(
        0, firstStarts.size() - 1
    );
    std::uniform_int_distribution<size_t> firstEndPick(
        0, firstEnds.size() - 1
    );
    std::uniform_int_distribution<size_t> surnameStartPick(
        0, surnameStarts.size() - 1
    );
    std::uniform_int_distribution<size_t> surnameEndPick(
        0, surnameEnds.size() - 1
    );

    // The base lists are preferred, but fictional candidates are mixed in
    // randomly so the generated account names do not look like a fixed list.
    for (int attempt = 0;
        attempt < 5000 && uniqueFirstNames.size() < firstNames.size() + 500;
        ++attempt)
    {
        const std::string candidate =
            firstStarts[firstStartPick(generator)] +
            firstEnds[firstEndPick(generator)];

        const std::string key = normalizeName(candidate);

        if (usedFirstNames.find(key) == usedFirstNames.end() &&
            seenFirstNames.insert(key).second)
        {
            uniqueFirstNames.push_back(candidate);
        }
    }

    for (int attempt = 0;
        attempt < 5000 && uniqueLastNames.size() < lastNames.size() + 500;
        ++attempt)
    {
        const std::string candidate =
            surnameStarts[surnameStartPick(generator)] +
            surnameEnds[surnameEndPick(generator)];

        const std::string key = normalizeName(candidate);

        if (usedLastNames.find(key) == usedLastNames.end() &&
            seenLastNames.insert(key).second)
        {
            uniqueLastNames.push_back(candidate);
        }
    }

    const auto unusedNames = [&](std::vector<std::string>& names,
        const std::unordered_set<std::string>& used)
    {
        names.erase(std::remove_if(names.begin(), names.end(), [&](const std::string& name)
        {
            return used.find(normalizeName(name)) != used.end();
        }), names.end());
    };
    unusedNames(uniqueFirstNames, usedFirstNames);
    unusedNames(uniqueLastNames, usedLastNames);

    if (uniqueFirstNames.empty() || uniqueLastNames.empty())
        return {};

    std::uniform_int_distribution<size_t> firstPick(0, uniqueFirstNames.size() - 1);
    std::uniform_int_distribution<size_t> lastPick(0, uniqueLastNames.size() - 1);
    return { uniqueFirstNames[firstPick(generator)], uniqueLastNames[lastPick(generator)] };
}

// ============================================================
// DEVICE AUTOMATION
// ============================================================

AutomationResult RunPhotonAutomation(
    const ADBDevice& device,
    std::ostream& log,
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

    log << "\nINITIAL DELAY: " << INITIAL_DELAY_MS << " ms\n";

    if (!PauseAutomation(INITIAL_DELAY_MS))
        return result;

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
    bool firstNameFieldConfirmed = false;
    POINT firstNameCenter{};
    std::string firstNameFieldDiagnostic;

    for (int attempt = 1; attempt <= 2; ++attempt)
    {
        log
            << "Login attempt "
            << attempt << "/2 using dedicated login-button mouse method\n";

        std::string tapDiagnostic;

        if (!TapLoginButton(
            device.id,
            loginCenter.x,
            loginCenter.y,
            attempt,
            tapDiagnostic))
        {
            log << "ERROR: " << tapDiagnostic << "\n";
            return result;
        }

        log << tapDiagnostic << "\n";

        // Check the actual next-stage field first. On the observed game
        // screen this appears immediately after login, so this avoids wasting
        // the full legacy-template timeout on a screen that has already changed.
        firstNameFieldConfirmed = WaitForInputField(
            device.id,
            "enter_name",
            firstNameCenter,
            firstNameFieldDiagnostic,
            5000
        );

        if (firstNameFieldConfirmed)
        {
            log << "LOGIN TRANSITION CONFIRMED BY NAME FIELD. "
                << firstNameFieldDiagnostic << "\n";
            result.loginConfirmed = true;
            break;
        }

        log << "Name field not confirmed yet: "
            << firstNameFieldDiagnostic << "\n";

        // Keep compatibility with versions where an intermediate screen is
        // displayed before the name-entry form.
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

            const bool stillVisible = DetectPhotonReady(
                device.id,
                retryConfidence,
                retryCenter,
                retryDiagnostic
            );

            log << "Login-button state after failed transition check: "
                << retryDiagnostic << "\n";

            if (stillVisible)
            {
                loginCenter = retryCenter;
                if (!PauseAutomation(180))
                    return result;
            }
            else
            {
                // The login button disappeared, so do not click its old
                // coordinates again. The screen changed, but the expected
                // name field was not confirmed.
                break;
            }
        }
    }

    if (!result.loginConfirmed)
    {
        log << "FAILED: Login transition not confirmed. "
            << "Neither the post-login template nor enter_name.png was confirmed.\n";
        return result;
    }

    // --------------------------------------------------------
    // STEP 3: CLEAR NAME AND IMMEDIATELY INPUT NEW NAME
    // --------------------------------------------------------

    log << "\n[3] FIND FIRST-NAME FIELD FROM enter_name.png\n";

    std::string nameDiagnostic;
    if (firstNameFieldConfirmed)
    {
        nameDiagnostic = firstNameFieldDiagnostic;
        log << "Using the name field already confirmed after login.\n";
    }
    else if (!WaitForInputField(
        device.id,
        "enter_name",
        firstNameCenter,
        nameDiagnostic,
        18000))
    {
        log << "FIRST NAME FIELD NOT FOUND: " << nameDiagnostic << "\n";
        return result;
    }

    log << nameDiagnostic << "\n";

    auto generatedName = GenerateRoleplayName(device.id);
    const std::string firstName = generatedName.first;
    const std::string lastName = generatedName.second;

    if (firstName.empty() || lastName.empty())
    {
        log
            << "ERROR: Could not create a new unique name/surname pair. "
            << "Check SmartClick_Names.txt on the Desktop; "
            << "the history may be inaccessible or the candidate pool exhausted.\n";
        return result;
    }

    log << "\nGENERATED UNIQUE FIRST NAME: " << firstName << "\n";
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
    if (!PauseAutomation(350))
        return result;

    std::string inputDiagnostic;
    if (!InputADBText(device.id, firstName, inputDiagnostic))
    {
        log << "FIRST NAME INPUT ERROR: " << inputDiagnostic << "\n";
        return result;
    }

    log << "FIRST NAME INPUT: " << inputDiagnostic << "\n";
    if (!PauseAutomation(180))
        return result;

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
        5000))
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
    if (!PauseAutomation(350))
        return result;

    log << "\nGENERATED LAST NAME: " << lastName << "\n";

    if (!InputADBText(device.id, lastName, inputDiagnostic))
    {
        log << "LAST NAME INPUT ERROR: " << inputDiagnostic << "\n";
        return result;
    }

    log << "LAST NAME INPUT: " << inputDiagnostic << "\n";
    if (!PauseAutomation(180))
        return result;

    // --------------------------------------------------------
    // STEP 5: CONFIRM INPUT COMMANDS
    // --------------------------------------------------------

    log << "\n[5] NAME AND SURNAME INPUT COMMANDS SENT\n";

    // UIAutomator may not expose individual WebView fields.
    result.nameEntered = true;
    result.surnameEntered = true;

    // --------------------------------------------------------
    // STEP 6: SAVE GENERATED NAME TO DESKTOP
    // --------------------------------------------------------

    log << "\n[6] SAVE GENERATED NAME\n";

    std::string saveDiagnostic;

    if (!SaveGeneratedName(
        firstName,
        lastName,
        saveDiagnostic))
    {
        log
            << "ERROR: " << saveDiagnostic << "\n"
            << "Registration stopped to avoid reusing an identity that "
            << "could not be saved to the uniqueness history.\n";
        return result;
    }
    else
    {
        log << saveDiagnostic << "\n";
    }

    // --------------------------------------------------------
    // STEP 7: CLICK PLAY AFTER ENTERING THE NEW NAME
    // --------------------------------------------------------

    log << "\n[7] WAIT FOR PLAY BUTTON\n";

    if (!WaitAndTapStage(device.id, "play", log))
    {
        log << "FAILED: could not detect/click the Play button after name entry.\n";
        return result;
    }

    if (!PauseAutomation(250))
        return result;

    // --------------------------------------------------------
    // STEP 8: WAIT FOR PASSWORD FIELD
    // --------------------------------------------------------

    log << "\n[8] WAIT FOR PASSWORD FIELD\n";

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

    // Let the password control finish its transition and receive focus.
    if (!PauseAutomation(900))
        return result;

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
    // STEP 9: WAIT FOR PASSWORD REPEAT FIELD
    // --------------------------------------------------------

    log << "\n[9] WAIT FOR PASSWORD REPEAT FIELD\n";

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

    // The repeat-password screen can animate for roughly two seconds.
    // Wait before typing and do not reactivate the window after tapping the field.
    if (!PauseAutomation(1400))
        return result;

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
    // STEP 10: REGISTER
    // --------------------------------------------------------

    log << "\n[10] WAIT FOR REGISTER BUTTON\n";

    if (!WaitAndTapStage(device.id, "register", log))
        return result;

    // --------------------------------------------------------
    // STEP 11: SKIP
    // --------------------------------------------------------

    log << "\n[11] WAIT FOR SKIP BUTTON\n";

    if (!WaitAndTapStage(device.id, "skip", log))
        return result;

    result.registrationCompleted = true;

    // --------------------------------------------------------
    // STEP 12: NEXT
    // --------------------------------------------------------

    log << "\n[12] WAIT FOR NEXT BUTTON\n";

    if (!WaitAndTapStage(device.id, "next", log))
        return result;

    // --------------------------------------------------------
    // STEP 13: START
    // --------------------------------------------------------

    log << "\n[13] WAIT FOR START BUTTON\n";

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

std::string RunAutomationBatch(const std::vector<ADBDevice>& devices, const std::string& password)
{
    std::vector<bool> primarySucceeded(devices.size());
    size_t completed = 0;
    size_t failed = 0;

    LivePhotonLogBuffer logBuffer;
    std::ostream log(&logBuffer);
    log << "Devices are processed sequentially because Windows input is shared.\n";

    for (size_t i = 0; i < devices.size() && !IsAutomationCancelled(); ++i)
    {
        try
        {
            primarySucceeded[i] = RunPhotonAutomation(devices[i], log, password).success;
        }
        catch (const std::exception& error)
        {
            log << "Automation failed: " << error.what() << "\n";
        }
        catch (...)
        {
            log << "Unknown automation error.\n";
        }
        if (!primarySucceeded[i] && !IsAutomationCancelled())
            ++failed;
        log << "[" << devices[i].id << "] Registration and startup: "
            << (primarySucceeded[i] ? "completed" : IsAutomationCancelled() ? "cancelled" : "failed") << "\n";
    }

    for (size_t i = 0; i < devices.size() && !IsAutomationCancelled(); ++i)
    {
        if (!primarySucceeded[i])
            continue;

        log << "\nPost-automation on " << devices[i].id << "\n";
        bool succeeded = false;
        try
        {
            succeeded = RunPostAutomationImageSequence(devices[i].id, log);
        }
        catch (const std::exception& error)
        {
            log << "Post-automation failed: " << error.what() << "\n";
        }
        catch (...)
        {
            log << "Unknown post-automation error.\n";
        }
        if (succeeded)
            ++completed;
        else if (!IsAutomationCancelled())
            ++failed;
    }

    const size_t cancelled = devices.size() - completed - failed;
    std::string summary = "Completed: " + std::to_string(completed) +
        ", failed: " + std::to_string(failed) +
        ", cancelled: " + std::to_string(cancelled) + ".";
    log << "\n" << summary << "\n";
    return summary;
}

void StartPhotonAutomation()
{
    if (g_AutomationBusy || g_ADBJob.valid())
        return;

    if (g_ADBStatus == "ADB error" || g_ADBStatus == "Invalid ADB output")
    {
        g_Notification = "Refresh the ADB device list before starting automation.";
        AppendPhotonLog("[START BLOCKED] ADB device list is out of date.\n");
        return;
    }

    if (!g_TemplatesLoaded)
    {
        g_Notification = "Login templates are missing.";
        AppendPhotonLog("[START BLOCKED] Login templates are missing.\n");
        return;
    }

    if (!AreAllStageTemplatesLoaded())
    {
        g_Notification =
            "Some registration PNG templates are missing.";
        AppendPhotonLog(
            "[START BLOCKED] Registration templates are missing.\n" +
            g_TemplateStatus + "\n"
        );
        return;
    }

    if (!IsSafeADBText(g_RegistrationPassword))
    {
        g_Notification =
            "Enter a registration password using English letters and digits.";
        AppendPhotonLog(
            "[START BLOCKED] Password must use English letters and digits only.\n"
        );
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
        AppendPhotonLog("[START BLOCKED] No ADB devices selected.\n");
        return;
    }

    // A single selected window is a convenient default for a single device.
    if (selectedDevices.size() == 1 &&
        !IsWindow(selectedDevices[0].automationWindow) &&
        g_SelectedWindow >= 0 &&
        g_SelectedWindow < static_cast<int>(g_EmulatorWindows.size()))
    {
        selectedDevices[0].automationWindow =
            g_EmulatorWindows[g_SelectedWindow].handle;
    }

    // Validate all explicit device-to-window mappings before starting.
    std::vector<HWND> usedWindows;

    for (const ADBDevice& device : selectedDevices)
    {
        if (device.status != "device")
            continue;

        const bool listed = std::any_of(g_EmulatorWindows.begin(), g_EmulatorWindows.end(),
            [&](const EmulatorWindow& window) { return window.handle == device.automationWindow; });
        if (!listed || !IsWindow(device.automationWindow))
        {
            g_Notification =
                "Assign an LDPlayer window to each selected ADB device "
                "in Emulator Manager.";

            AppendPhotonLog(
                "[START BLOCKED] No valid LDPlayer window assigned to device " +
                device.id + ".\n"
            );
            return;
        }

        if (std::find(
            usedWindows.begin(),
            usedWindows.end(),
            device.automationWindow) != usedWindows.end())
        {
            g_Notification =
                "Each selected ADB device must use a different LDPlayer window.";

            AppendPhotonLog(
                "[START BLOCKED] The same LDPlayer window is assigned to more "
                "than one selected ADB device.\n"
            );
            return;
        }

        usedWindows.push_back(device.automationWindow);
    }

    if (usedWindows.empty())
    {
        g_Notification = "Select at least one ready ADB device.";
        AppendPhotonLog("[START BLOCKED] No selected device is ready.\n");
        return;
    }

    if (g_AutomationThread.joinable())
        g_AutomationThread.join();

    std::string passwordSnapshot = g_RegistrationPassword;
    {
        std::lock_guard<std::mutex> lock(g_LogMutex);
        g_PhotonDetectionLog.clear();
        g_PhotonDetectionLog =
            "Starting PHOTON automation with REAL WINDOWS INPUT...\n";
    }

    {
        std::lock_guard<std::mutex> lock(g_DeviceWindowMapMutex);
        g_DeviceWindowMap.clear();

        for (const ADBDevice& device : selectedDevices)
        {
            WindowIdentity identity;
            identity.handle = device.automationWindow;
            GetWindowThreadProcessId(identity.handle, &identity.processId);
            g_DeviceWindowMap.emplace(device.id, identity);
        }
    }

    g_CancelAutomation = false;
    g_AutomationBusy = true;
    g_Notification = "PHOTON automation is running.";

    try
    {
        g_AutomationThread = std::thread(
            [devices = std::move(selectedDevices), password = std::move(passwordSnapshot)]
            {
                struct BusyReset
                {
                    ~BusyReset() { g_AutomationBusy = false; }
                } reset;

                try
                {
                    g_AutomationNotification = RunAutomationBatch(devices, password);
                }
                catch (...)
                {
                    g_AutomationNotification = "Automation stopped because of an unexpected error.";
                }
            });
    }
    catch (const std::exception& error)
    {
        g_AutomationBusy = false;
        g_Notification = std::string("Cannot start automation: ") + error.what();
        AppendPhotonLog(g_Notification + "\n");
    }
}

// ============================================================
// ADB DEVICE MANAGER
// ============================================================

void ApplyADBDeviceList(std::string output)
{
    g_ADBOutput = std::move(output);
    if (IsADBError(g_ADBOutput))
    {
        g_ADBStatus = "ADB error";
        g_Notification = "Cannot execute ADB. See the ADB log.";
        return;
    }

    std::vector<ADBDevice> refreshed;
    std::unordered_set<std::string> seen;
    std::istringstream stream(g_ADBOutput);
    std::string line;
    bool hasHeader = false;
    while (std::getline(stream, line))
    {
        line = Trim(line);
        if (line == "List of devices attached")
        {
            hasHeader = true;
            continue;
        }
        if (!hasHeader || line.empty() || line.front() == '*')
            continue;

        std::istringstream fields(line);
        ADBDevice device;
        if (!(fields >> device.id >> device.status) || !seen.insert(device.id).second)
            continue;

        if (device.status == "no")
            device.status = "no permissions";
        device.model = GetModelFromLine(line);
        const auto previous = std::find_if(g_Devices.begin(), g_Devices.end(),
            [&](const ADBDevice& entry) { return entry.id == device.id; });
        if (previous != g_Devices.end())
        {
            device.selected = previous->selected;
            device.automationWindow = previous->automationWindow;
        }
        refreshed.push_back(std::move(device));
    }

    if (!hasHeader)
    {
        g_ADBStatus = "Invalid ADB output";
        g_Notification = "ADB did not return a device list.";
        return;
    }

    g_Devices = std::move(refreshed);
    const bool hasReadyDevice = std::any_of(g_Devices.begin(), g_Devices.end(),
        [](const ADBDevice& device) { return device.status == "device"; });
    if (g_Devices.empty())
        g_ADBStatus = "No devices found";
    else
        g_ADBStatus = hasReadyDevice ? "Connected" : "No devices ready";
    g_Notification = "ADB device list updated.";
}

void RefreshADBDevices()
{
    if (g_ADBJob.valid() || g_AutomationBusy)
        return;

    try
    {
        g_ADBJob = std::async(std::launch::async, []
        {
            AdbJobResult result;
            result.output = ExecuteADB(L"devices -l");
            return result;
        });
        g_ADBStatus = "Checking ADB...";
    }
    catch (const std::exception& error)
    {
        g_ADBStatus = "ADB error";
        g_Notification = std::string("Cannot start device refresh: ") + error.what();
    }
}

void LaunchPhotonOnSelectedDevices()
{
    if (g_ADBJob.valid() || g_AutomationBusy)
        return;

    if (g_ADBStatus == "ADB error" || g_ADBStatus == "Invalid ADB output")
    {
        g_Notification = "Refresh the ADB device list before launching PHOTON.";
        return;
    }

    std::vector<ADBDevice> selected;
    for (const ADBDevice& device : g_Devices)
    {
        if (device.selected)
            selected.push_back(device);
    }

    if (selected.empty())
    {
        g_Notification = "Select at least one ADB device.";
        return;
    }

    try
    {
        g_ADBJob = std::async(std::launch::async, [selected = std::move(selected)]
        {
            AdbJobResult result;
            result.launch = true;
            std::ostringstream log;
            size_t launched = 0;
            for (const ADBDevice& device : selected)
            {
                if (g_ShutdownRequested)
                    break;
                log << "[" << device.id << "] ";
                if (device.status != "device")
                {
                    log << "Skipped. Device is " << device.status << ".\n";
                    continue;
                }

                const std::string output = ExecuteADB(
                    L"-s " + DeviceArgument(device.id) +
                    L" shell monkey -p com.photon.top -c android.intent.category.LAUNCHER 1");
                log << (output.empty() ? "ADB returned empty output." : Trim(output)) << "\n";
                if (!IsADBError(output) &&
                    output.find("Events injected: 1") != std::string::npos)
                {
                    ++launched;
                }
            }
            result.output = log.str();
            result.notification = "PHOTON launch confirmed: " + std::to_string(launched) +
                " of " + std::to_string(selected.size()) + ".";
            return result;
        });
        g_PhotonLaunchLog = "Launching PHOTON...";
        g_Notification = g_PhotonLaunchLog;
    }
    catch (const std::exception& error)
    {
        g_Notification = std::string("Cannot start PHOTON launch: ") + error.what();
    }
}

void PollBackgroundJobs()
{
    if (!g_AutomationBusy && g_AutomationThread.joinable())
    {
        g_AutomationThread.join();
        g_Notification = std::move(g_AutomationNotification);
    }

    if (!g_ADBJob.valid() ||
        g_ADBJob.wait_for(std::chrono::milliseconds(0)) != std::future_status::ready)
        return;

    try
    {
        AdbJobResult result = g_ADBJob.get();
        if (result.launch)
        {
            g_PhotonLaunchLog = std::move(result.output);
            g_Notification = std::move(result.notification);
        }
        else
        {
            ApplyADBDeviceList(std::move(result.output));
        }
    }
    catch (const std::exception& error)
    {
        if (g_ADBStatus == "Checking ADB...")
            g_ADBStatus = "ADB error";
        g_Notification = std::string("ADB background task failed: ") + error.what();
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

    const int copied = GetWindowTextW(hwnd, title.data(), length + 1);
    if (copied <= 0)
        return TRUE;
    title.resize(static_cast<size_t>(copied));

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
    const HWND previouslySelected =
        g_SelectedWindow >= 0 && g_SelectedWindow < static_cast<int>(g_EmulatorWindows.size())
        ? g_EmulatorWindows[g_SelectedWindow].handle : nullptr;
    g_EmulatorWindows.clear();
    g_SelectedWindow = -1;

    EnumWindows(EnumEmulatorWindows, 0);
    for (size_t i = 0; i < g_EmulatorWindows.size(); ++i)
    {
        if (g_EmulatorWindows[i].handle == previouslySelected)
            g_SelectedWindow = static_cast<int>(i);
    }
    if (g_EmulatorWindows.size() == 1)
        g_SelectedWindow = 0;

    g_Notification = "Emulator windows refreshed";
}

void RefreshEverything()
{
    RefreshEmulatorWindows();
    RefreshADBDevices();
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
    ImGui::TextDisabled(
        "Assign the matching LDPlayer window to every device. "
        "Mouse and keyboard input will be visible on the desktop."
    );
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

            ImGui::SameLine();
            ImGui::SetNextItemWidth(240.0f);

            std::string mappedWindowLabel = "Assign LDPlayer window";
            for (size_t windowIndex = 0;
                windowIndex < g_EmulatorWindows.size();
                ++windowIndex)
            {
                if (g_EmulatorWindows[windowIndex].handle ==
                    device.automationWindow)
                {
                    mappedWindowLabel =
                        std::to_string(windowIndex + 1) + ". " +
                        WideToUtf8(g_EmulatorWindows[windowIndex].title);
                    break;
                }
            }

            if (ImGui::BeginCombo(
                "##ldplayer_mapping",
                mappedWindowLabel.c_str()))
            {
                for (size_t windowIndex = 0;
                    windowIndex < g_EmulatorWindows.size();
                    ++windowIndex)
                {
                    const EmulatorWindow& candidate =
                        g_EmulatorWindows[windowIndex];

                    std::string option =
                        std::to_string(windowIndex + 1) + ". " +
                        WideToUtf8(candidate.title);

                    const bool isSelected =
                        device.automationWindow == candidate.handle;

                    if (ImGui::Selectable(option.c_str(), isSelected))
                        device.automationWindow = candidate.handle;

                    if (isSelected)
                        ImGui::SetItemDefaultFocus();
                }

                ImGui::EndCombo();
            }

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

    ImGui::BeginDisabled(g_ADBJob.valid() || g_AutomationBusy);
    if (ImGui::Button("START PHOTON", ImVec2(220, 48)))
        LaunchPhotonOnSelectedDevices();
    ImGui::EndDisabled();

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

    ImGui::TextWrapped("Selected emulators run sequentially.");

    ImGui::Spacing();

    if (g_AutomationBusy)
    {
        ImGui::BeginDisabled(g_CancelAutomation);
        if (ImGui::Button(g_CancelAutomation ? "STOPPING..." : "STOP AUTOMATION", ImVec2(260, 48)))
        {
            g_CancelAutomation = true;
            g_Notification = "Stopping automation...";
        }
        ImGui::EndDisabled();
    }
    else
    {
        ImGui::BeginDisabled(g_ADBJob.valid());
        if (ImGui::Button("START FULL AUTOMATION", ImVec2(260, 48)))
            StartPhotonAutomation();
        ImGui::EndDisabled();
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

    if (ImGui::Button("COPY LOG", ImVec2(130, 30)))
    {
        std::string completeLog = detectionLogCopy;

        if (!g_PhotonLaunchLog.empty())
        {
            if (!completeLog.empty())
                completeLog += "\n\n";

            completeLog += "========== PHOTON LAUNCH LOG ==========\n";
            completeLog += g_PhotonLaunchLog;
        }

        if (completeLog.empty())
            completeLog = "SmartClick log is empty.";

        ImGui::SetClipboardText(completeLog.c_str());
        g_Notification = "Log copied to clipboard.";
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
        "Live automation diagnostics and ADB activity"
    );

    ImGui::TextWrapped("%s", g_Notification.c_str());

    ImGui::Spacing();

    std::string automationLog;
    {
        std::lock_guard<std::mutex> lock(g_LogMutex);
        automationLog = g_PhotonDetectionLog;
    }

    ImGui::Text(
        "PHOTON AUTOMATION LOG%s",
        g_AutomationBusy.load() ? "  [RUNNING]" : ""
    );

    ImGui::SameLine();

    if (ImGui::SmallButton("Clear log") &&
        !g_AutomationBusy.load())
    {
        std::lock_guard<std::mutex> lock(g_LogMutex);
        g_PhotonDetectionLog.clear();
        automationLog.clear();
    }

    ImGui::BeginChild(
        "PhotonLiveLog",
        ImVec2(0, -115),
        true,
        ImGuiWindowFlags_HorizontalScrollbar
    );

    const bool wasAtBottom =
        ImGui::GetScrollY() >= ImGui::GetScrollMaxY() - 8.0f;

    if (automationLog.empty())
    {
        ImGui::TextDisabled(
            "Automation log is empty. Start PHOTON to see live diagnostics."
        );
    }
    else
    {
        ImGui::TextUnformatted(automationLog.c_str());
    }

    if (wasAtBottom || g_AutomationBusy.load())
        ImGui::SetScrollHereY(1.0f);

    ImGui::EndChild();

    ImGui::Spacing();
    ImGui::Text("LAST ADB OUTPUT");

    ImGui::BeginChild(
        "ADBLogOutput",
        ImVec2(0, 85),
        true,
        ImGuiWindowFlags_HorizontalScrollbar
    );

    if (g_ADBOutput.empty())
        ImGui::TextDisabled("No ADB output yet.");
    else
        ImGui::TextUnformatted(g_ADBOutput.c_str());

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

HRESULT CreateRenderTarget()
{
    ID3D11Texture2D* backBuffer = nullptr;
    HRESULT result = g_pSwapChain->GetBuffer(0, IID_PPV_ARGS(&backBuffer));
    if (FAILED(result))
        return result;

    result = g_pd3dDevice->CreateRenderTargetView(backBuffer, nullptr, &g_mainRenderTargetView);
    backBuffer->Release();
    return result;
}

void CleanupRenderTarget()
{
    if (g_mainRenderTargetView)
    {
        g_mainRenderTargetView->Release();
        g_mainRenderTargetView = nullptr;
    }
}

HRESULT CreateDeviceD3D(HWND hwnd)
{
    DXGI_SWAP_CHAIN_DESC swapChainDesc{};

    swapChainDesc.BufferCount = 2;

    swapChainDesc.BufferDesc.Format =
        DXGI_FORMAT_R8G8B8A8_UNORM;

    swapChainDesc.BufferDesc.RefreshRate.Numerator = 60;
    swapChainDesc.BufferDesc.RefreshRate.Denominator = 1;

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

    const auto create = [&](D3D_DRIVER_TYPE driver)
    {
        return D3D11CreateDeviceAndSwapChain(
            nullptr, driver, nullptr, createFlags,
            featureLevels, ARRAYSIZE(featureLevels), D3D11_SDK_VERSION,
            &swapChainDesc, &g_pSwapChain, &g_pd3dDevice, &featureLevel, &g_pd3dDeviceContext);
    };

    HRESULT result = create(D3D_DRIVER_TYPE_HARDWARE);
    if (result == DXGI_ERROR_SDK_COMPONENT_MISSING && createFlags != 0)
    {
        createFlags = 0;
        result = create(D3D_DRIVER_TYPE_HARDWARE);
    }
    if (FAILED(result))
        result = create(D3D_DRIVER_TYPE_WARP);

    return FAILED(result) ? result : CreateRenderTarget();
}

HRESULT ApplyPendingResize()
{
    if (!g_PendingWidth || !g_PendingHeight)
        return S_OK;

    g_pd3dDeviceContext->OMSetRenderTargets(0, nullptr, nullptr);
    CleanupRenderTarget();
    const HRESULT result = g_pSwapChain->ResizeBuffers(
        0, g_PendingWidth, g_PendingHeight, DXGI_FORMAT_UNKNOWN, 0);
    g_PendingWidth = 0;
    g_PendingHeight = 0;
    return FAILED(result) ? result : CreateRenderTarget();
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
    if (ImGui::GetCurrentContext() && ImGui_ImplWin32_WndProcHandler(hWnd, msg, wParam, lParam))
    {
        return true;
    }

    switch (msg)
    {
    case WM_SIZE:
        g_Minimized = wParam == SIZE_MINIMIZED;
        if (!g_Minimized)
        {
            g_PendingWidth = LOWORD(lParam);
            g_PendingHeight = HIWORD(lParam);
        }
        return 0;

    case WM_SYSCOMMAND:
        if ((wParam & 0xfff0) == SC_KEYMENU)
            return 0;

        break;

    case WM_DESTROY:
        g_ShutdownRequested = true;
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
    ImGui_ImplWin32_EnableDpiAwareness();

    WNDCLASSEXW wc{};

    wc.cbSize = sizeof(WNDCLASSEXW);
    wc.style = CS_CLASSDC;
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInstance;
    wc.lpszClassName = L"SmartClickWindow";

    if (!RegisterClassExW(&wc))
        return 1;

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

    HRESULT graphicsResult = CreateDeviceD3D(g_hWnd);
    if (FAILED(graphicsResult))
    {
        MessageBoxW(g_hWnd, L"Could not initialize Direct3D 11.", L"SmartClick", MB_OK | MB_ICONERROR);
        CleanupDeviceD3D();
        DestroyWindow(g_hWnd);
        UnregisterClassW(wc.lpszClassName, wc.hInstance);
        return 1;
    }
    g_PendingWidth = 0;
    g_PendingHeight = 0;

    IMGUI_CHECKVERSION();
    ImGui::CreateContext();
    ImGui::GetIO().ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard;
    SetupImGuiStyle();

    const bool platformReady = ImGui_ImplWin32_Init(g_hWnd);
    if (!platformReady || !ImGui_ImplDX11_Init(g_pd3dDevice, g_pd3dDeviceContext))
    {
        MessageBoxW(g_hWnd, L"Could not initialize the interface.", L"SmartClick", MB_OK | MB_ICONERROR);
        if (platformReady)
            ImGui_ImplWin32_Shutdown();
        ImGui::DestroyContext();
        CleanupDeviceD3D();
        DestroyWindow(g_hWnd);
        UnregisterClassW(wc.lpszClassName, wc.hInstance);
        return 1;
    }

    ShowWindow(g_hWnd, SW_SHOWDEFAULT);
    UpdateWindow(g_hWnd);

    LoadPhotonTemplates();
    RefreshEverything();

    MSG msg{};
    bool occluded = false;
    while (g_Running)
    {
        while (PeekMessageW(
            &msg,
            nullptr,
            0U,
            0U,
            PM_REMOVE))
        {
            if (msg.message == WM_QUIT)
            {
                g_Running = false;
                break;
            }
            TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }

        if (!g_Running)
            break;

        PollBackgroundJobs();
        if (g_Minimized)
        {
            Sleep(20);
            continue;
        }

        graphicsResult = ApplyPendingResize();
        if (FAILED(graphicsResult))
            break;

        if (occluded)
        {
            graphicsResult = g_pSwapChain->Present(0, DXGI_PRESENT_TEST);
            if (FAILED(graphicsResult))
                break;
            if (graphicsResult == DXGI_STATUS_OCCLUDED)
            {
                Sleep(20);
                continue;
            }
            occluded = false;
        }

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

        graphicsResult = g_pSwapChain->Present(1, 0);
        if (FAILED(graphicsResult))
            break;
        occluded = graphicsResult == DXGI_STATUS_OCCLUDED;
    }

    g_ShutdownRequested = true;
    if (g_AutomationThread.joinable())
        g_AutomationThread.join();
    if (g_ADBJob.valid())
        g_ADBJob.wait();

    ImGui_ImplDX11_Shutdown();
    ImGui_ImplWin32_Shutdown();

    ImGui::DestroyContext();

    CleanupDeviceD3D();

    if (FAILED(graphicsResult))
        MessageBoxW(g_hWnd, L"Direct3D rendering failed. Restart SmartClick.", L"SmartClick", MB_OK | MB_ICONERROR);

    DestroyWindow(g_hWnd);
    UnregisterClassW(wc.lpszClassName, wc.hInstance);
    return FAILED(graphicsResult) ? 1 : 0;
}
