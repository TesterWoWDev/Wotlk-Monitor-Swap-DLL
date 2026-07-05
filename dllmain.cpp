#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <winioctl.h>
#include <cstdlib>
#include <cstring>
#include <cfloat>
#include <cstdio>
#include <cstdarg>

// --- MANDATORY PROXY EXPORTS ---
// IMPORTANT: this list must match DivxDecoder_org.dll's REAL export table
// exactly (currently just these 4 -- verified via VerifyDivxForwarding's
// log output and static PE inspection). Earlier revisions also forwarded
// DivxCreate/DivxDestroy/DivxGetVersion/GetVideoProps, none of which
// exist on the real decoder -- those were dead forwards (GetProcAddress
// on them always failed). Keeping the export set 1:1 identical to the
// original is what actually matters for the loader to treat this as a
// drop-in replacement.
#pragma comment(linker, "/export:DivxDecode=DivxDecoder_org.DivxDecode")
#pragma comment(linker, "/export:SetOutputFormat=DivxDecoder_org.SetOutputFormat")
#pragma comment(linker, "/export:InitializeDivxDecoder=DivxDecoder_org.InitializeDivxDecoder")
#pragma comment(linker, "/export:UnInitializeDivxDecoder=DivxDecoder_org.UnInitializeDivxDecoder")

typedef struct lua_State lua_State;

// ============================================================
// Lua C-API function pointers
// ============================================================
#define ADDR_REGISTER   0x00817F90
#define ADDR_PUSHNUMBER 0x0084E2A0

typedef void (__cdecl* LuaPushNumberFn)(lua_State*, double);
typedef void (__cdecl* RegisterFnT)(const char*, int(__cdecl*)(lua_State*));

static LuaPushNumberFn  pPushNumber = nullptr;
static RegisterFnT      pRegister   = nullptr;

static volatile bool g_running = true;

// Forward declaration
static void ResolveLuaAPI();

// Handle to this DLL's own module, needed early for building file paths
// (debug log, saved-resolutions config) next to the DLL.
static HMODULE g_hSelfModule = nullptr;

// ============================================================
// Monitor state
// ============================================================
static CRITICAL_SECTION g_monitorLock;

struct MonitorInfo {
    HMONITOR handle;
    RECT     rect;
    char     device[32]; // stable Windows device name, e.g. "\\.\DISPLAY1" -
                         // used as the persistence key instead of the
                         // enumeration index, which can shift between sessions
};

#define MAX_MONITORS 16
static MonitorInfo g_monitors[MAX_MONITORS];
static int         g_monitorCount   = 0;
static int         g_currentMonitor = 0; // 1-based index, 0 = unknown
static int         g_pendingMonitor = 0; // monitor to switch to on ApplyMonitor

// EnumDisplayMonitors callback — collects all monitors
static BOOL CALLBACK MonitorEnumProc(HMONITOR hMon, HDC, LPRECT rc, LPARAM) {
    if (g_monitorCount >= MAX_MONITORS) return TRUE;
    g_monitors[g_monitorCount].handle = hMon;
    g_monitors[g_monitorCount].rect   = *rc;
    MONITORINFOEXA mi = {};
    mi.cbSize = sizeof(mi);
    if (GetMonitorInfoA(hMon, &mi)) {
        strncpy(g_monitors[g_monitorCount].device, mi.szDevice, sizeof(g_monitors[g_monitorCount].device) - 1);
    } else {
        g_monitors[g_monitorCount].device[0] = '\0';
    }
    g_monitorCount++;
    return TRUE;
}

// ============================================================
// Lightweight debug log (next to the DLL) so we can see what's actually
// happening at each step without needing to guess from in-game symptoms.
// ============================================================
static CRITICAL_SECTION g_logLock;
static bool g_logLockInit = false;

static void GetDebugLogPath(char* outPath, size_t outSize) {
    char modPath[MAX_PATH] = {};
    if (g_hSelfModule) GetModuleFileNameA(g_hSelfModule, modPath, MAX_PATH);
    char* lastSlash = strrchr(modPath, '\\');
    if (lastSlash) *(lastSlash + 1) = '\0'; else modPath[0] = '\0';
    outPath[0] = '\0';
    strncat(outPath, modPath, outSize - 1);
    strncat(outPath, "MonitorDebug.log", outSize - strlen(outPath) - 1);
}

static void DbgLog(const char* fmt, ...) {
    if (g_logLockInit) EnterCriticalSection(&g_logLock);
    char path[MAX_PATH] = {};
    GetDebugLogPath(path, sizeof(path));
    FILE* f = fopen(path, "a");
    if (f) {
        SYSTEMTIME st; GetLocalTime(&st);
        fprintf(f, "[%02d:%02d:%02d.%03d] ", st.wHour, st.wMinute, st.wSecond, st.wMilliseconds);
        va_list args;
        va_start(args, fmt);
        vfprintf(f, fmt, args);
        va_end(args);
        fprintf(f, "\n");
        fclose(f);
    }
    if (g_logLockInit) LeaveCriticalSection(&g_logLock);
}

// Shared helper: find the WoW window belonging to this process.
//
// IMPORTANT: we do NOT match on window title text anymore. The previous
// approach required the title to contain "World of Warcraft" or "Wow",
// but many clients/realms/launchers rename the window title (custom
// branding, localized text, etc.) -- if the title never matches, this
// function permanently returns NULL no matter how long we retry, which
// silently breaks the entire DLL (nothing ever registers). Since this
// DLL is injected specifically into the WoW process, ANY visible,
// non-owned top-level window belonging to this exact process is for all
// practical purposes the game window -- so we just pick the LARGEST one
// (the game's render window will always dwarf any small helper/tooltip
// window that might also exist).
static HWND FindWowWindow() {
    DWORD myPid = GetCurrentProcessId();
    struct EnumWnd { DWORD pid; HWND found; long bestArea; char bestTitle[128]; };
    EnumWnd ew = { myPid, NULL, -1, {0} };
    EnumWindows([](HWND h, LPARAM lp) -> BOOL {
        EnumWnd* d = (EnumWnd*)lp;
        DWORD pid = 0; GetWindowThreadProcessId(h, &pid);
        if (pid == d->pid && IsWindowVisible(h) && GetWindow(h, GW_OWNER) == NULL) {
            RECT r = {};
            GetWindowRect(h, &r);
            long area = (long)(r.right - r.left) * (long)(r.bottom - r.top);
            if (area > d->bestArea) {
                d->bestArea = area;
                d->found = h;
                GetWindowTextA(h, d->bestTitle, sizeof(d->bestTitle) - 1);
            }
        }
        return TRUE;
    }, (LPARAM)&ew);
    static char s_lastLoggedTitle[128] = {0};
    static HWND s_lastLoggedHwnd = NULL;
    if (ew.found && (ew.found != s_lastLoggedHwnd || strcmp(ew.bestTitle, s_lastLoggedTitle) != 0)) {
        s_lastLoggedHwnd = ew.found;
        strncpy(s_lastLoggedTitle, ew.bestTitle, sizeof(s_lastLoggedTitle) - 1);
        DbgLog("FindWowWindow: picked hwnd=%p area=%ld title=\"%s\"", (void*)ew.found, ew.bestArea, ew.bestTitle);
    }
    return ew.found;
}

// ============================================================
// Per-monitor resolution persistence
// ============================================================
// Remembers the last resolution actually used on each physical
// monitor (keyed by its stable Windows device name, e.g.
// "\\.\DISPLAY1" - NOT by enumeration index, which can shift between
// sessions if monitors are (re)detected in a different order). Saved
// to a small text file next to this DLL so it survives game restarts.
// If a monitor has no saved entry yet (first time ever, or an older
// DLL build without this feature), callers fall back to whatever
// resolution Windows itself currently reports for that monitor (i.e.
// the monitor's rect from EnumDisplayMonitors, which already reflects
// the desktop resolution the user configured for it in Windows).

struct SavedRes { char device[32]; int width; int height; };
#define MAX_SAVED_RES 16
static SavedRes g_savedRes[MAX_SAVED_RES];
static int      g_savedResCount = 0;

static void GetMonitorResConfigPath(char* outPath, size_t outSize) {
    char modPath[MAX_PATH] = {};
    if (g_hSelfModule) GetModuleFileNameA(g_hSelfModule, modPath, MAX_PATH);
    char* lastSlash = strrchr(modPath, '\\');
    if (lastSlash) *(lastSlash + 1) = '\0'; else modPath[0] = '\0';
    outPath[0] = '\0';
    strncat(outPath, modPath, outSize - 1);
    strncat(outPath, "MonitorResolutions.cfg", outSize - strlen(outPath) - 1);
}

static void LoadSavedResolutions() {
    g_savedResCount = 0;
    char path[MAX_PATH] = {};
    GetMonitorResConfigPath(path, sizeof(path));
    FILE* f = fopen(path, "r");
    if (!f) return;
    char line[128];
    while (fgets(line, sizeof(line), f) && g_savedResCount < MAX_SAVED_RES) {
        char* eq = strchr(line, '=');
        if (!eq) continue;
        *eq = '\0';
        char* devPart = line;
        char* resPart = eq + 1;
        char* x = strchr(resPart, 'x');
        if (!x) continue;
        *x = '\0';
        int w = atoi(resPart);
        int h = atoi(x + 1);
        if (w <= 0 || h <= 0) continue;
        strncpy(g_savedRes[g_savedResCount].device, devPart, sizeof(g_savedRes[g_savedResCount].device) - 1);
        g_savedRes[g_savedResCount].width  = w;
        g_savedRes[g_savedResCount].height = h;
        g_savedResCount++;
    }
    fclose(f);
}

static void SaveSavedResolutionsToFile() {
    char path[MAX_PATH] = {};
    GetMonitorResConfigPath(path, sizeof(path));
    FILE* f = fopen(path, "w");
    if (!f) return;
    for (int i = 0; i < g_savedResCount; i++) {
        fprintf(f, "%s=%dx%d\n", g_savedRes[i].device, g_savedRes[i].width, g_savedRes[i].height);
    }
    fclose(f);
}

static bool FindSavedResolution(const char* device, int* outW, int* outH) {
    if (!device || !device[0]) return false;
    for (int i = 0; i < g_savedResCount; i++) {
        if (strcmp(g_savedRes[i].device, device) == 0) {
            *outW = g_savedRes[i].width;
            *outH = g_savedRes[i].height;
            return true;
        }
    }
    return false;
}

static void SetSavedResolution(const char* device, int w, int h) {
    if (!device || !device[0] || w <= 0 || h <= 0) return;
    for (int i = 0; i < g_savedResCount; i++) {
        if (strcmp(g_savedRes[i].device, device) == 0) {
            if (g_savedRes[i].width == w && g_savedRes[i].height == h) return; // unchanged
            g_savedRes[i].width  = w;
            g_savedRes[i].height = h;
            SaveSavedResolutionsToFile();
            return;
        }
    }
    if (g_savedResCount < MAX_SAVED_RES) {
        strncpy(g_savedRes[g_savedResCount].device, device, sizeof(g_savedRes[g_savedResCount].device) - 1);
        g_savedRes[g_savedResCount].width  = w;
        g_savedRes[g_savedResCount].height = h;
        g_savedResCount++;
        SaveSavedResolutionsToFile();
    }
}

// ============================================================
// Last-selected-monitor persistence
// ============================================================
// Remembers WHICH monitor (by its stable Windows device name, e.g.
// "\\.\DISPLAY2") the window was last placed on, so we can put it back
// there automatically the next time WoW starts -- instead of only
// remembering per-monitor resolutions once the player has already
// switched at least once per session.
//
// Stored as a plain text file (just the device name, one line) at
// <GameRoot>\WTF\MonitorCount.txt. The path is discovered dynamically via
// GetModuleFileNameA(NULL, ...), which returns the path of the currently
// running EXE (Wow.exe) regardless of where this DLL itself sits on disk
// or which drive/folder the game is installed in -- nothing here is
// hard-coded to a specific install location.
//
// If the file is missing, empty, unreadable, or names a device that no
// longer exists this session (deleted cache, monitor unplugged, first
// run ever, etc.) this is a silent no-op: we simply keep whatever
// monitor the window naturally opened on, exactly like before this
// feature existed. Nothing here is required for the DLL to function.
static char g_savedMonitorDevice[32] = {0};

static void GetGameRootWtfFilePath(char* outPath, size_t outSize, const char* filename) {
    char exePath[MAX_PATH] = {};
    // NULL => path of the main EXE of the CURRENT PROCESS (Wow.exe), not
    // this DLL's own path -- this is what lets us find "<GameRoot>\WTF"
    // without ever hard-coding a drive letter or folder name.
    GetModuleFileNameA(NULL, exePath, MAX_PATH);
    char* lastSlash = strrchr(exePath, '\\');
    if (lastSlash) *(lastSlash + 1) = '\0'; else exePath[0] = '\0';

    char wtfDir[MAX_PATH] = {};
    strncpy(wtfDir, exePath, sizeof(wtfDir) - 1);
    strncat(wtfDir, "WTF", sizeof(wtfDir) - strlen(wtfDir) - 1);
    CreateDirectoryA(wtfDir, NULL); // no-op if it already exists (it always should)

    outPath[0] = '\0';
    strncat(outPath, wtfDir, outSize - 1);
    strncat(outPath, "\\", outSize - strlen(outPath) - 1);
    strncat(outPath, filename, outSize - strlen(outPath) - 1);
}

static void LoadSavedMonitorSelection() {
    g_savedMonitorDevice[0] = '\0';
    char path[MAX_PATH] = {};
    GetGameRootWtfFilePath(path, sizeof(path), "MonitorCount.txt");
    FILE* f = fopen(path, "r");
    if (!f) return;
    char line[64] = {};
    if (fgets(line, sizeof(line), f)) {
        size_t len = strlen(line);
        while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r' || line[len - 1] == ' '))
            line[--len] = '\0';
        strncpy(g_savedMonitorDevice, line, sizeof(g_savedMonitorDevice) - 1);
    }
    fclose(f);
}

static void SaveSavedMonitorSelection(const char* device) {
    if (!device || !device[0]) return;
    if (strcmp(g_savedMonitorDevice, device) == 0) return; // unchanged, skip disk write
    strncpy(g_savedMonitorDevice, device, sizeof(g_savedMonitorDevice) - 1);
    char path[MAX_PATH] = {};
    GetGameRootWtfFilePath(path, sizeof(path), "MonitorCount.txt");
    FILE* f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "%s\n", device);
    fclose(f);
}

// ============================================================
// Window-creation-time monitor placement (IAT hook)
// ============================================================
// Everything above only reacts AFTER the WoW window already exists
// (WaitForWoWReady -> MoveWindowToMonitor), which means the window is
// briefly visible on whatever monitor Windows/WoW picked by default
// (usually the primary one) before we yank it over to the saved
// monitor a moment later -- a visible flash/jump.
//
// To avoid that, we hook Wow.exe's own Import Address Table entry for
// USER32.dll!CreateWindowExA (and the Unicode variant, in case this
// build was linked against that instead) so we can rewrite the X/Y
// position of the call BEFORE the window is actually created -- it
// simply never appears anywhere except the saved monitor in the first
// place. This must be installed as early as possible in
// DLL_PROCESS_ATTACH, before Wow.exe has had any chance to create its
// main window.
//
// This is pure IAT patching (rewrite one function pointer in Wow.exe's
// own import table) -- no external hooking library needed, and it only
// touches Wow.exe's table, never USER32.dll itself, so nothing else in
// the process is affected.
typedef HWND (WINAPI* CreateWindowExA_t)(
    DWORD dwExStyle, LPCSTR lpClassName, LPCSTR lpWindowName, DWORD dwStyle,
    int X, int Y, int nWidth, int nHeight,
    HWND hWndParent, HMENU hMenu, HINSTANCE hInstance, LPVOID lpParam);
typedef HWND (WINAPI* CreateWindowExW_t)(
    DWORD dwExStyle, LPCWSTR lpClassName, LPCWSTR lpWindowName, DWORD dwStyle,
    int X, int Y, int nWidth, int nHeight,
    HWND hWndParent, HMENU hMenu, HINSTANCE hInstance, LPVOID lpParam);

static CreateWindowExA_t g_origCreateWindowExA = nullptr;
static CreateWindowExW_t g_origCreateWindowExW = nullptr;

// Same idea, but returns the FULL rect (origin + size) of the monitor
// matching g_savedMonitorDevice in one call. This is what the
// CreateWindowExA/W hooks actually need: overriding X/Y alone (as an
// earlier version of this hook did) places the window in the right
// SPOT but WoW still creates it at whatever size it was already going
// to use (observed in practice to be some other monitor's native size,
// e.g. the primary display's 3840x2160 -- NOT driven by the gxResolution
// CVar, which is why pre-patching Config.wtf alone doesn't fix this).
// That means the window is born positioned correctly but sized wrong,
// straddling/overflowing the real target monitor until something
// resizes it a moment later -- exactly the visible "wrong size for a
// couple seconds" bug this is meant to eliminate. Overriding width and
// height too, right here at creation time, means there is nothing left
// to correct after the fact.
static bool GetSavedMonitorRect(int* outX, int* outY, int* outW, int* outH) {
    if (!g_savedMonitorDevice[0]) return false;
    struct FindCtx { const char* device; bool found; RECT rc; };
    FindCtx ctx = { g_savedMonitorDevice, false, {} };
    EnumDisplayMonitors(NULL, NULL, [](HMONITOR hMon, HDC, LPRECT rc, LPARAM lp) -> BOOL {
        FindCtx* c = (FindCtx*)lp;
        MONITORINFOEXA mi = {}; mi.cbSize = sizeof(mi);
        if (GetMonitorInfoA(hMon, &mi) && strcmp(mi.szDevice, c->device) == 0) {
            c->found = true;
            c->rc = *rc;
            return FALSE;
        }
        return TRUE;
    }, (LPARAM)&ctx);
    if (ctx.found) {
        *outX = ctx.rc.left;
        *outY = ctx.rc.top;
        *outW = ctx.rc.right  - ctx.rc.left;
        *outH = ctx.rc.bottom - ctx.rc.top;
        return true;
    }
    DbgLog("GetSavedMonitorRect: saved device \"%s\" not found among currently enumerated monitors", g_savedMonitorDevice);
    return false;
}

// Same idea, but returns the target monitor's native WIDTH/HEIGHT (its
// current Windows desktop resolution) instead of its origin. Used to
// pre-correct Config.wtf's gxResolution CVar (see
// PatchConfigResolutionForSavedMonitor below) before Wow.exe ever reads
// it, so the very first frame already renders at the right size for
// whichever monitor the window is about to be born on -- instead of
// booting at the WRONG (e.g. primary monitor's) native resolution and
// only correcting itself a couple of seconds later once WoW's own
// engine notices the mismatch (the visible resize/flicker this whole
// mechanism exists to avoid).
static bool GetSavedMonitorNativeSize(int* outW, int* outH) {
    if (!g_savedMonitorDevice[0]) return false;
    struct FindCtx { const char* device; bool found; int w, h; };
    FindCtx ctx = { g_savedMonitorDevice, false, 0, 0 };
    EnumDisplayMonitors(NULL, NULL, [](HMONITOR hMon, HDC, LPRECT rc, LPARAM lp) -> BOOL {
        FindCtx* c = (FindCtx*)lp;
        MONITORINFOEXA mi = {}; mi.cbSize = sizeof(mi);
        if (GetMonitorInfoA(hMon, &mi) && strcmp(mi.szDevice, c->device) == 0) {
            c->found = true;
            c->w = rc->right  - rc->left;
            c->h = rc->bottom - rc->top;
            return FALSE;
        }
        return TRUE;
    }, (LPARAM)&ctx);
    if (ctx.found) { *outW = ctx.w; *outH = ctx.h; return true; }
    return false;
}

// Rewrites the "SET gxResolution \"WxH\"" line inside WTF\Config.wtf (see
// GetGameRootWtfFilePath above for how that path is found without any
// hard-coded drive/folder) so it already matches the SAVED monitor's
// native resolution, BEFORE Wow.exe's own startup code gets a chance to
// read this file and create its window/D3D device from it.
//
// Why this matters: gxMaximize ("Windowed Maximized") does NOT stop WoW
// from initializing its backbuffer at whatever size gxResolution says --
// it only affects how the WINDOW itself is sized/positioned. If the
// player's last-used monitor has a different native resolution than
// whatever gxResolution happened to be left at (e.g. from the PRIMARY
// monitor, which is where WoW would otherwise default to), the engine
// visibly renders at the wrong size for a couple of seconds until it
// notices the mismatch and self-corrects -- exactly the delay this DLL
// is meant to eliminate. By fixing the CVar up-front, the very first
// frame is already correct and no runtime SetScreenResolution() call
// (with its own visible gx-restart) is ever needed for a normal launch.
//
// Deliberately conservative: only touches the single gxResolution line,
// leaves every other line/setting byte-for-byte untouched, and is a
// total no-op if there's no saved monitor yet, the monitor can't be
// found this session, the file is missing, or the CVar line isn't
// present for some reason (fresh account, corrupted file, etc.) --
// WoW just uses whatever Config.wtf already says, same as before this
// feature existed.
static void PatchConfigResolutionForSavedMonitor() {
    int nativeW = 0, nativeH = 0;
    if (!GetSavedMonitorNativeSize(&nativeW, &nativeH) || nativeW <= 0 || nativeH <= 0) return;

    char path[MAX_PATH] = {};
    GetGameRootWtfFilePath(path, sizeof(path), "Config.wtf");

    FILE* f = fopen(path, "rb");
    if (!f) return;
    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (size <= 0 || size > 65536) { fclose(f); return; } // sanity guard, Config.wtf is always tiny
    char* buf = (char*)malloc((size_t)size + 1);
    if (!buf) { fclose(f); return; }
    size_t readBytes = fread(buf, 1, (size_t)size, f);
    fclose(f);
    buf[readBytes] = '\0';

    char wantedLine[64] = {};
    _snprintf(wantedLine, sizeof(wantedLine) - 1, "SET gxResolution \"%dx%d\"", nativeW, nativeH);

    char* linePtr = strstr(buf, "SET gxResolution \"");
    if (!linePtr) { free(buf); return; } // CVar not present -- leave file alone

    char* lineEnd = strchr(linePtr, '\n');
    size_t lineLen = lineEnd ? (size_t)(lineEnd - linePtr) : strlen(linePtr);
    if (lineLen > 0 && linePtr[lineLen - 1] == '\r') lineLen--; // tolerate CRLF

    if (lineLen == strlen(wantedLine) && strncmp(linePtr, wantedLine, lineLen) == 0) {
        free(buf); // already correct, nothing to rewrite
        return;
    }

    size_t prefixLen     = (size_t)(linePtr - buf);
    size_t suffixOffset  = prefixLen + lineLen;
    FILE* out = fopen(path, "wb");
    if (!out) { free(buf); return; }
    fwrite(buf, 1, prefixLen, out);
    fwrite(wantedLine, 1, strlen(wantedLine), out);
    fwrite(buf + suffixOffset, 1, readBytes - suffixOffset, out);
    fclose(out);

    DbgLog("PatchConfigResolutionForSavedMonitor: rewrote gxResolution -> %dx%d (monitor=%s)",
           nativeW, nativeH, g_savedMonitorDevice);
    free(buf);
}

// Heuristic for "is this the game's own main top-level window": no
// parent (rules out child controls/dialogs), reasonably large (rules
// out tooltips/IME helper windows/small popups), and belongs to the
// EXE itself rather than some other loaded module. We can't match on
// class name or title (same reasoning as FindWowWindow above -- custom
// clients/branding can't be relied on), so size + ownership is the
// most robust signal available at creation time.
static bool LooksLikeMainGameWindow(HWND hWndParent, int nWidth, int nHeight, HINSTANCE hInstance) {
    // CW_USEDEFAULT is (int)0x80000000 -- a huge negative number when read
    // as a plain int. A naive "nWidth >= 400" check rejects it outright,
    // which would silently defeat this whole heuristic on any WoW build
    // that asks Windows to pick the default size/position for its main
    // window (rare in practice for this client, but cheap to handle
    // correctly rather than assume it never happens). Treat CW_USEDEFAULT
    // as an acceptable size on either axis instead of rejecting it.
    bool widthOk  = (nWidth  == CW_USEDEFAULT) || (nWidth  >= 400);
    bool heightOk = (nHeight == CW_USEDEFAULT) || (nHeight >= 300);
    return (hWndParent == NULL) && widthOk && heightOk &&
           (hInstance == NULL || hInstance == GetModuleHandleA(NULL));
}

static HWND WINAPI HookedCreateWindowExA(
    DWORD dwExStyle, LPCSTR lpClassName, LPCSTR lpWindowName, DWORD dwStyle,
    int X, int Y, int nWidth, int nHeight,
    HWND hWndParent, HMENU hMenu, HINSTANCE hInstance, LPVOID lpParam)
{
    if (LooksLikeMainGameWindow(hWndParent, nWidth, nHeight, hInstance)) {
        int mx = 0, my = 0, mw = 0, mh = 0;
        if (GetSavedMonitorRect(&mx, &my, &mw, &mh)) {
            DbgLog("HookedCreateWindowExA: redirecting window creation from (%d,%d) size=%dx%d to saved monitor rect (%d,%d) size=%dx%d class=\"%s\"",
                   X, Y, nWidth, nHeight, mx, my, mw, mh, lpClassName ? lpClassName : "(null)");
            X = mx;
            Y = my;
            nWidth  = mw;
            nHeight = mh;
        }
    }
    return g_origCreateWindowExA(dwExStyle, lpClassName, lpWindowName, dwStyle,
                                  X, Y, nWidth, nHeight, hWndParent, hMenu, hInstance, lpParam);
}

static HWND WINAPI HookedCreateWindowExW(
    DWORD dwExStyle, LPCWSTR lpClassName, LPCWSTR lpWindowName, DWORD dwStyle,
    int X, int Y, int nWidth, int nHeight,
    HWND hWndParent, HMENU hMenu, HINSTANCE hInstance, LPVOID lpParam)
{
    if (LooksLikeMainGameWindow(hWndParent, nWidth, nHeight, hInstance)) {
        int mx = 0, my = 0, mw = 0, mh = 0;
        if (GetSavedMonitorRect(&mx, &my, &mw, &mh)) {
            DbgLog("HookedCreateWindowExW: redirecting window creation from (%d,%d) size=%dx%d to saved monitor rect (%d,%d) size=%dx%d",
                   X, Y, nWidth, nHeight, mx, my, mw, mh);
            X = mx;
            Y = my;
            nWidth  = mw;
            nHeight = mh;
        }
    }
    return g_origCreateWindowExW(dwExStyle, lpClassName, lpWindowName, dwStyle,
                                  X, Y, nWidth, nHeight, hWndParent, hMenu, hInstance, lpParam);
}

// Patches ONE IAT entry (for the given import name) belonging to
// user32.dll inside Wow.exe's own import table to point at newFn,
// returning the original function pointer (or nullptr on failure).
// Never touches USER32.dll itself -- only Wow.exe's table of pointers
// into it -- so nothing else in the process is affected.
static void* PatchExeIatEntry(const char* importName, void* newFn) {
    HMODULE hExe = GetModuleHandleA(NULL);
    if (!hExe) return nullptr;

    void* result = nullptr;
    __try {
        BYTE* base = (BYTE*)hExe;
        IMAGE_DOS_HEADER* dos = (IMAGE_DOS_HEADER*)base;
        if (dos->e_magic != IMAGE_DOS_SIGNATURE) return nullptr;
        IMAGE_NT_HEADERS* nt = (IMAGE_NT_HEADERS*)(base + dos->e_lfanew);
        if (nt->Signature != IMAGE_NT_SIGNATURE) return nullptr;

        IMAGE_DATA_DIRECTORY impDir = nt->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT];
        if (impDir.VirtualAddress == 0) return nullptr;

        IMAGE_IMPORT_DESCRIPTOR* imp = (IMAGE_IMPORT_DESCRIPTOR*)(base + impDir.VirtualAddress);
        for (; imp->Name; imp++) {
            const char* moduleName = (const char*)(base + imp->Name);
            if (lstrcmpiA(moduleName, "user32.dll") != 0) continue;

            IMAGE_THUNK_DATA* origThunk = (IMAGE_THUNK_DATA*)(base + (imp->OriginalFirstThunk ? imp->OriginalFirstThunk : imp->FirstThunk));
            IMAGE_THUNK_DATA* firstThunk = (IMAGE_THUNK_DATA*)(base + imp->FirstThunk);

            for (; origThunk->u1.AddressOfData; origThunk++, firstThunk++) {
                if (IMAGE_SNAP_BY_ORDINAL(origThunk->u1.Ordinal)) continue;
                IMAGE_IMPORT_BY_NAME* byName = (IMAGE_IMPORT_BY_NAME*)(base + origThunk->u1.AddressOfData);
                if (strcmp((const char*)byName->Name, importName) != 0) continue;

                result = (void*)firstThunk->u1.Function;

                DWORD oldProtect = 0;
                if (VirtualProtect(&firstThunk->u1.Function, sizeof(void*), PAGE_READWRITE, &oldProtect)) {
                    firstThunk->u1.Function = (ULONG_PTR)newFn;
                    VirtualProtect(&firstThunk->u1.Function, sizeof(void*), oldProtect, &oldProtect);
                } else {
                    DbgLog("PatchExeIatEntry: VirtualProtect failed for %s", importName);
                    result = nullptr;
                }
                return result;
            }
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        DbgLog("PatchExeIatEntry: exception while patching %s", importName);
        return nullptr;
    }
    return result;
}

// Installs both hooks (A and W variants -- whichever Wow.exe actually
// imports; the other one simply won't be found and is silently
// skipped). Safe/harmless to call even if g_savedMonitorDevice is empty
// (the hooked functions just pass through unchanged in that case).
static void InstallCreateWindowHook() {
    void* origA = PatchExeIatEntry("CreateWindowExA", (void*)HookedCreateWindowExA);
    if (origA) {
        g_origCreateWindowExA = (CreateWindowExA_t)origA;
        DbgLog("InstallCreateWindowHook: hooked CreateWindowExA, orig=%p", origA);
    } else {
        DbgLog("InstallCreateWindowHook: CreateWindowExA not found/hooked in Wow.exe IAT");
    }

    void* origW = PatchExeIatEntry("CreateWindowExW", (void*)HookedCreateWindowExW);
    if (origW) {
        g_origCreateWindowExW = (CreateWindowExW_t)origW;
        DbgLog("InstallCreateWindowHook: hooked CreateWindowExW, orig=%p", origW);
    } else {
        DbgLog("InstallCreateWindowHook: CreateWindowExW not found/hooked in Wow.exe IAT");
    }
}

// ============================================================
// Main-thread-safe Lua registration
// ============================================================
// CRITICAL: the Lua VM is NOT thread-safe. Calling FrameScript_RegisterFunction
// (pRegister) from a background thread while the game's main thread is
// concurrently running Lua/UI code corrupts the Lua state and causes random,
// hard-to-diagnose crashes (different stack traces every time). All Lua-API
// touching calls MUST happen on the game's main thread. We guarantee this by
// subclassing the WoW window: Windows always dispatches a window's messages
// on the thread that owns the window (the main thread), so doing the actual
// registration inside the window procedure is safe.
static WNDPROC        g_origWndProc    = nullptr;
static volatile bool  g_needsRegister  = false;

static void RegisterAllLuaFunctions(); // fwd decl, defined after the L_* functions

static LRESULT CALLBACK HookedWndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    if (g_needsRegister) {
        g_needsRegister = false; // clear first: registration itself may pump messages
        RegisterAllLuaFunctions();
    }
    if (g_origWndProc) return CallWindowProc(g_origWndProc, hwnd, msg, wParam, lParam);
    return DefWindowProc(hwnd, msg, wParam, lParam);
}

static void InstallWndProcHook(HWND hwnd) {
    if (!hwnd || g_origWndProc) return;
    g_origWndProc = (WNDPROC)SetWindowLongPtrA(hwnd, GWLP_WNDPROC, (LONG_PTR)HookedWndProc);
}

// Refresh the monitor list and detect which one the WoW window is on
static void RefreshMonitors() {
    EnterCriticalSection(&g_monitorLock);
    g_monitorCount = 0;
    EnumDisplayMonitors(NULL, NULL, MonitorEnumProc, 0);

    // Find the WoW window
    HWND wowWnd = FindWowWindow();

    // Determine which monitor index the window is on
    g_currentMonitor = 0;
    if (wowWnd) {
        HMONITOR hCur = MonitorFromWindow(wowWnd, MONITOR_DEFAULTTONEAREST);
        for (int i = 0; i < g_monitorCount; i++) {
            if (g_monitors[i].handle == hCur) {
                g_currentMonitor = i + 1; // 1-based
                break;
            }
        }
    }
    if (g_pendingMonitor == 0) {
        g_pendingMonitor = g_currentMonitor;
    }
    LeaveCriticalSection(&g_monitorLock);
}

// Move the WoW window to a given monitor (1-based index).
//
// IMPORTANT: we always resize the window to exactly fill the target
// monitor's rect (instead of just centering the *old* window size on
// the new monitor). The old "center, keep size" approach broke as
// soon as the source and target monitors had different resolutions:
// the window would keep whatever size it had on the previous monitor
// (e.g. sized for a 3840x2160 display) and get centered on a monitor
// with different bounds, so it visually spilled over onto whichever
// monitor happened to sit next to it (never hard-code which one -
// Windows' monitor enumeration order has nothing to do with physical
// left-to-right placement). Filling the target monitor's rect exactly
// guarantees the window can never straddle two displays, regardless
// of resolution mismatches, and matches how windowed-maximized mode
// is expected to behave anyway.

// Reads the actual current client-area size of the WoW window (i.e.
// the resolution the game is really rendering at right now).
static void GetWowClientSize(int* outW, int* outH) {
    *outW = 0; *outH = 0;
    HWND wnd = FindWowWindow();
    if (!wnd) return;
    RECT cr = {};
    GetClientRect(wnd, &cr);
    *outW = cr.right  - cr.left;
    *outH = cr.bottom - cr.top;
}

static bool MoveWindowToMonitor(int monitorIndex) {
    EnterCriticalSection(&g_monitorLock);
    if (monitorIndex < 1 || monitorIndex > g_monitorCount) {
        LeaveCriticalSection(&g_monitorLock);
        return false;
    }

    HWND wowWnd = FindWowWindow();
    if (!wowWnd) {
        LeaveCriticalSection(&g_monitorLock);
        return false;
    }

    // Before leaving the current monitor, remember what resolution it
    // was actually using, keyed to ITS device name, so next time we
    // come back to it we can restore that resolution automatically.
    if (g_currentMonitor >= 1 && g_currentMonitor <= g_monitorCount &&
        g_currentMonitor != monitorIndex) {
        int curW = 0, curH = 0;
        GetWowClientSize(&curW, &curH);
        if (curW > 0 && curH > 0) {
            SetSavedResolution(g_monitors[g_currentMonitor - 1].device, curW, curH);
        }
    }

    RECT mon = g_monitors[monitorIndex - 1].rect;
    int monW  = mon.right  - mon.left;
    int monH  = mon.bottom - mon.top;
    char targetDevice[32] = {};
    strncpy(targetDevice, g_monitors[monitorIndex - 1].device, sizeof(targetDevice) - 1);

    g_currentMonitor = monitorIndex;
    g_pendingMonitor = monitorIndex;
    LeaveCriticalSection(&g_monitorLock);

    // Remember this monitor as "the one to use next time", keyed by its
    // stable device name (see LoadSavedMonitorSelection above).
    SaveSavedMonitorSelection(targetDevice);

    // SetWindowPos runs outside the lock: it can pump window messages
    // (WM_WINDOWPOSCHANGED etc.) re-entrantly, and we must never call
    // back into a critical section we're already holding.
    SetWindowPos(wowWnd, NULL, mon.left, mon.top, monW, monH,
                 SWP_NOZORDER | SWP_NOACTIVATE);

    return true;
}

// ============================================================
// Memory safety helpers
// ============================================================
static bool IsValidCodeAddress(void* addr) {
    if (!addr) return false;
    if ((UINT_PTR)addr < 0x00010000) return false;
    if ((UINT_PTR)addr > 0x7FFFFFFF) return false;
    MEMORY_BASIC_INFORMATION mbi = {};
    if (!VirtualQuery(addr, &mbi, sizeof(mbi))) return false;
    if (mbi.State != MEM_COMMIT) return false;
    return !(mbi.Protect & (PAGE_NOACCESS | PAGE_GUARD));
}
static void SafePushNumber(lua_State* L, double v) {
    if (!pPushNumber || !IsValidCodeAddress((void*)pPushNumber)) return;
    __try { pPushNumber(L, v); } __except(EXCEPTION_EXECUTE_HANDLER) {}
}
static int SafeRegister(const char* name, int(__cdecl* cfn)(lua_State*)) {
    if (!pRegister || !IsValidCodeAddress((void*)pRegister)) return 0;
    __try { pRegister(name, cfn); } __except(EXCEPTION_EXECUTE_HANDLER) { return 0; }
    return 1;
}

// ============================================================
// Lua API — Monitor functions
// ============================================================

// Returns total number of monitors detected by Windows
static int L_GetMonitorCount(lua_State* L) {
    EnterCriticalSection(&g_monitorLock);
    double count = (double)g_monitorCount;
    LeaveCriticalSection(&g_monitorLock);
    SafePushNumber(L, count);
    return 1;
}

// Returns current monitor index (1-based) that the WoW window is on
static int L_GetCurrentMonitor(lua_State* L) {
    EnterCriticalSection(&g_monitorLock);
    double cur = (double)g_currentMonitor;
    LeaveCriticalSection(&g_monitorLock);
    SafePushNumber(L, cur);
    return 1;
}

// Advances pending monitor to the next one (wraps around), returns new pending index
static int L_NextMonitor(lua_State* L) {
    EnterCriticalSection(&g_monitorLock);
    if (g_monitorCount > 0) {
        if (g_pendingMonitor < 1) g_pendingMonitor = g_currentMonitor;
        g_pendingMonitor = (g_pendingMonitor % g_monitorCount) + 1;
    }
    double pending = (double)g_pendingMonitor;
    LeaveCriticalSection(&g_monitorLock);
    SafePushNumber(L, pending);
    return 1;
}

// Moves pending monitor to the previous one (wraps around), returns new pending index
static int L_PrevMonitor(lua_State* L) {
    EnterCriticalSection(&g_monitorLock);
    if (g_monitorCount > 0) {
        if (g_pendingMonitor < 1) g_pendingMonitor = g_currentMonitor;
        g_pendingMonitor = g_pendingMonitor - 1;
        if (g_pendingMonitor < 1) g_pendingMonitor = g_monitorCount;
    }
    double pending = (double)g_pendingMonitor;
    LeaveCriticalSection(&g_monitorLock);
    SafePushNumber(L, pending);
    return 1;
}

// Applies the pending monitor — actually moves the WoW window
// Returns 1 on success, 0 on failure
static int L_ApplyMonitor(lua_State* L) {
    EnterCriticalSection(&g_monitorLock);
    int target = g_pendingMonitor;
    LeaveCriticalSection(&g_monitorLock);
    bool ok = MoveWindowToMonitor(target);
    SafePushNumber(L, ok ? 1.0 : 0.0);
    return 1;
}

// SetMonitor(): applies whatever is currently pending (set via NextMonitor/PrevMonitor).
// Kept for backward compatibility with ApplyMonitor-style call sites.
// Returns the applied monitor index on success, 0 on failure.
static int L_SetMonitor(lua_State* L) {
    EnterCriticalSection(&g_monitorLock);
    int target = g_pendingMonitor;
    LeaveCriticalSection(&g_monitorLock);
    bool ok = MoveWindowToMonitor(target);
    SafePushNumber(L, ok ? (double)target : 0.0);
    return 1;
}

// Returns the width/height WoW should use for the PENDING (target)
// monitor: whatever resolution we remember was last actually used on
// that monitor, or - if we've never seen that monitor before - the
// resolution Windows itself is currently using for it (its rect from
// EnumDisplayMonitors). No arguments needed/possible (see note above
// L_NextMonitor about why we can't safely read Lua call arguments) -
// these always describe whatever monitor is currently pending.
static int L_GetPendingMonitorWidth(lua_State* L) {
    EnterCriticalSection(&g_monitorLock);
    double w = 0;
    int idx = g_pendingMonitor;
    if (idx >= 1 && idx <= g_monitorCount) {
        int sw = 0, sh = 0;
        if (FindSavedResolution(g_monitors[idx - 1].device, &sw, &sh)) {
            w = (double)sw;
        } else {
            w = (double)(g_monitors[idx - 1].rect.right - g_monitors[idx - 1].rect.left);
        }
    }
    LeaveCriticalSection(&g_monitorLock);
    SafePushNumber(L, w);
    return 1;
}
static int L_GetPendingMonitorHeight(lua_State* L) {
    EnterCriticalSection(&g_monitorLock);
    double h = 0;
    int idx = g_pendingMonitor;
    if (idx >= 1 && idx <= g_monitorCount) {
        int sw = 0, sh = 0;
        if (FindSavedResolution(g_monitors[idx - 1].device, &sw, &sh)) {
            h = (double)sh;
        } else {
            h = (double)(g_monitors[idx - 1].rect.bottom - g_monitors[idx - 1].rect.top);
        }
    }
    LeaveCriticalSection(&g_monitorLock);
    SafePushNumber(L, h);
    return 1;
}

// Same as above, but ALWAYS the monitor's native/Windows-desktop size --
// never the saved custom resolution. Needed for windowed-MAXIMIZED mode:
// WoW's own engine is supposed to native-fill automatically when Maximized
// is checked, but in practice it can take a couple of seconds to notice
// the monitor changed and catch up on its own. Explicitly forcing
// SetScreenResolution() to the target monitor's true native size (see
// Lua-side VideoOptionsResolutionPanel_ApplyMonitorResolution) makes that
// correction happen immediately instead of waiting on WoW's own lazy
// detection -- while still respecting "don't apply the SAVED per-monitor
// custom resolution while Maximized" (that part of the earlier fix was
// correct and stays as-is).
static int L_GetPendingMonitorNativeWidth(lua_State* L) {
    EnterCriticalSection(&g_monitorLock);
    double w = 0;
    int idx = g_pendingMonitor;
    if (idx >= 1 && idx <= g_monitorCount) {
        w = (double)(g_monitors[idx - 1].rect.right - g_monitors[idx - 1].rect.left);
    }
    LeaveCriticalSection(&g_monitorLock);
    SafePushNumber(L, w);
    return 1;
}
static int L_GetPendingMonitorNativeHeight(lua_State* L) {
    EnterCriticalSection(&g_monitorLock);
    double h = 0;
    int idx = g_pendingMonitor;
    if (idx >= 1 && idx <= g_monitorCount) {
        h = (double)(g_monitors[idx - 1].rect.bottom - g_monitors[idx - 1].rect.top);
    }
    LeaveCriticalSection(&g_monitorLock);
    SafePushNumber(L, h);
    return 1;
}

// Records whatever resolution the window is ACTUALLY using right now
// against the CURRENT monitor's device name, so we remember it for
// next time we switch to that monitor. Meant to be called from Lua
// after every gx restart (resolution change, vsync toggle, etc.),
// regardless of whether a monitor switch was involved.
static int L_SaveCurrentMonitorResolution(lua_State* L) {
    EnterCriticalSection(&g_monitorLock);
    if (g_currentMonitor >= 1 && g_currentMonitor <= g_monitorCount) {
        int w = 0, h = 0;
        GetWowClientSize(&w, &h);
        if (w > 0 && h > 0) {
            SetSavedResolution(g_monitors[g_currentMonitor - 1].device, w, h);
        }
    }
    LeaveCriticalSection(&g_monitorLock);
    SafePushNumber(L, 1.0);
    return 1;
}

// Lets Lua explicitly ask the DLL to re-register all functions right now
// (in addition to the automatic heartbeat re-registration). Safe to call
// from Lua: by the time this runs, we're already being invoked BY the
// current Lua VM on the main thread, so re-running registration here is
// synchronous and immediate (no need to round-trip through the
// g_needsRegister/WndProc-hook mechanism used for the very first call).
static int L_TriggerMonitorReRegister(lua_State* L) {
    RegisterAllLuaFunctions();
    SafePushNumber(L, 1.0);
    return 1;
}

// ============================================================
// WaitForWoWReady
// ============================================================
// IMPORTANT: this must never give up permanently. The window can take an
// unpredictable amount of time to appear (slow login/realm queue/char
// select), and if we stop retrying after a fixed timeout, the DLL's Lua
// functions (GetMonitorCount, ApplyMonitor, ...) simply never get
// registered for the rest of the session — with no error, just silent
// nil forever. So we poll indefinitely (until g_running goes false at
// DLL unload) instead of a bounded attempt count.
static HWND WaitForWoWReady() {
    HWND wowWnd = NULL;
    while (g_running) {
        wowWnd = FindWowWindow();
        if (wowWnd) break;
        Sleep(500);
    }
    return g_running ? wowWnd : NULL;
}

// All Lua registration calls, run ONLY from the main thread via HookedWndProc.
//
// IMPORTANT: this is called REPEATEDLY (heartbeat, see MainThread) for the
// entire lifetime of the process, not just once. WoW 3.3.5 uses a SEPARATE
// Lua VM for the glue screens (login/realm/char-select, "GlueXML") versus
// the in-world game screen ("FrameXML") -- pRegister has no explicit
// lua_State* parameter, which means WoW.exe itself tracks internally which
// VM is "current" and registers into that one. A registration made while
// still on the glue screen (which is typically where this DLL's window
// first appears, seconds after DLL_PROCESS_ATTACH) does NOT carry over into
// the game-world Lua state that addons actually run in, and is silently
// lost forever once that state is torn down. Rather than trying to detect
// the exact moment of the glue->world transition (or any subsequent
// /reload or loading-screen VM reset), we just re-issue registration on a
// steady heartbeat: SafeRegister-ing an already-registered name into
// whichever Lua state happens to be current is cheap and harmless, so this
// guarantees the functions eventually exist wherever addons can see them.
static void RegisterAllLuaFunctions() {
    ResolveLuaAPI();

    static int s_registerCallCount = 0;
    bool verbose = (s_registerCallCount == 0) || (s_registerCallCount % 15 == 0);
    s_registerCallCount++;

    if (verbose) {
        DbgLog("RegisterAllLuaFunctions: pRegister=%p (valid=%s) pPushNumber=%p (valid=%s)",
               (void*)pRegister, pRegister ? "yes" : "NO",
               (void*)pPushNumber, pPushNumber ? "yes" : "NO");
    }

    int okCount = 0, failCount = 0;
    #define COUNT_REG(r) do { if (r) okCount++; else failCount++; } while(0)

    // Monitor functions
    COUNT_REG(SafeRegister("GetMonitorCount",    L_GetMonitorCount));
    COUNT_REG(SafeRegister("GetCurrentMonitor",  L_GetCurrentMonitor));
    COUNT_REG(SafeRegister("NextMonitor",        L_NextMonitor));
    COUNT_REG(SafeRegister("PrevMonitor",        L_PrevMonitor));
    COUNT_REG(SafeRegister("ApplyMonitor",       L_ApplyMonitor));
    COUNT_REG(SafeRegister("SetMonitor",         L_SetMonitor));
    COUNT_REG(SafeRegister("GetPendingMonitorWidth",       L_GetPendingMonitorWidth));
    COUNT_REG(SafeRegister("GetPendingMonitorHeight",      L_GetPendingMonitorHeight));
    COUNT_REG(SafeRegister("GetPendingMonitorNativeWidth",  L_GetPendingMonitorNativeWidth));
    COUNT_REG(SafeRegister("GetPendingMonitorNativeHeight", L_GetPendingMonitorNativeHeight));
    COUNT_REG(SafeRegister("SaveCurrentMonitorResolution", L_SaveCurrentMonitorResolution));
    COUNT_REG(SafeRegister("TriggerMonitorReRegister",     L_TriggerMonitorReRegister));

    #undef COUNT_REG
    DbgLog("RegisterAllLuaFunctions: done, registered ok=%d failed=%d (out of %d)", okCount, failCount, okCount + failCount);
}

static DWORD WINAPI MainThread(LPVOID) {
    DbgLog("MainThread started, waiting for WoW window...");
    HWND wowWnd = WaitForWoWReady();
    if (!wowWnd) { DbgLog("MainThread: exiting without a window (shutdown)"); return 0; }
    DbgLog("MainThread: got window hwnd=%p, installing hook", (void*)wowWnd);

    // Refresh monitor list and hook up Lua registration IMMEDIATELY, as
    // soon as the window exists -- neither of these touches the WoW window
    // itself (RefreshMonitors is pure EnumDisplayMonitors; the WndProc hook
    // just subclasses message dispatch), so there's no reason to make them
    // wait for the D3D device to finish settling. Doing this early is what
    // lets GetMonitorCount()/GetPendingMonitorWidth()/etc. show up on the
    // glue-screen Lua VM within a second or so of the login screen
    // appearing, instead of several seconds later -- which is what was
    // making the per-monitor resolution restore feel slow to kick in.
    RefreshMonitors();
    DbgLog("MainThread: RefreshMonitors done, monitorCount=%d currentMonitor=%d", g_monitorCount, g_currentMonitor);

    InstallWndProcHook(wowWnd);
    DbgLog("MainThread: hook installed=%s (origWndProc=%p)", g_origWndProc ? "yes" : "no", (void*)g_origWndProc);
    g_needsRegister = true;

    // Give the engine a brief moment to finish settling its device/window
    // before we actually MOVE/RESIZE it below -- this is the one operation
    // that genuinely can conflict with a still-initializing D3D device.
    // Registration and monitor detection above already happened without
    // waiting for this, since neither of them touches the window.
    Sleep(1000);
    HWND recheckWnd = FindWowWindow();
    if (recheckWnd) wowWnd = recheckWnd;

    // Restore whichever monitor the player was last placed on, persisted at
    // <GameRoot>\WTF\MonitorCount.txt (see SaveSavedMonitorSelection /
    // LoadSavedMonitorSelection above). If the saved device doesn't match
    // any monitor detected THIS session (file missing/deleted, monitor
    // unplugged, first run ever, ...) this is a silent no-op and the window
    // just stays wherever it naturally opened -- never a hard requirement,
    // exactly like before this feature existed.
    if (g_savedMonitorDevice[0]) {
        EnterCriticalSection(&g_monitorLock);
        int target = 0;
        for (int i = 0; i < g_monitorCount; i++) {
            if (strcmp(g_monitors[i].device, g_savedMonitorDevice) == 0) { target = i + 1; break; }
        }
        LeaveCriticalSection(&g_monitorLock);
        if (target > 0 && target != g_currentMonitor) {
            DbgLog("MainThread: restoring saved monitor selection -> device=%s index=%d", g_savedMonitorDevice, target);
            MoveWindowToMonitor(target);
        }
    }

    // Heartbeat: keep re-arming g_needsRegister for as long as the process
    // lives, instead of stopping after the first successful registration.
    //
    // Why: WoW 3.3.5 uses a SEPARATE Lua VM for the glue screens
    // (login/realm/char-select) versus the actual in-world game screen.
    // The very first registration typically happens seconds after
    // DLL_PROCESS_ATTACH, while the player is still on the glue screen —
    // that registration is invisible to (and lost when leaving) the glue
    // VM, so addons running in-world would otherwise see GetMonitorCount
    // etc. as nil forever, with nothing left to ever retry. Re-arming this
    // every couple seconds guarantees registration eventually lands in
    // whichever Lua state is actually current (glue, world, and again after
    // every subsequent /reload or loading screen), at the cost of a little
    // redundant work once things are already registered.
    int waitedSec = 0;
    while (g_running) {
        Sleep(1000);
        waitedSec++;
        if (!IsWindow(wowWnd)) {
            HWND fresh = FindWowWindow();
            if (fresh && fresh != wowWnd) {
                DbgLog("MainThread: old window gone, re-hooking new hwnd=%p", (void*)fresh);
                wowWnd = fresh;
                g_origWndProc = nullptr; // allow re-hooking the new window
                InstallWndProcHook(wowWnd);
            }
        }
        // Every 2s, ask HookedWndProc to (re-)run registration on the main thread.
        if (waitedSec % 2 == 0) {
            g_needsRegister = true;
        }
        if (waitedSec % 30 == 0) {
            DbgLog("MainThread: heartbeat alive (%ds), window valid=%s",
                   waitedSec, IsWindow(wowWnd) ? "yes" : "no");
        }
    }

    return 0;
}

static void ResolveLuaAPI() {
    pRegister   = (RegisterFnT)     ADDR_REGISTER;
    pPushNumber = (LuaPushNumberFn) ADDR_PUSHNUMBER;
    if (!IsValidCodeAddress((void*)pRegister))   pRegister   = nullptr;
    if (!IsValidCodeAddress((void*)pPushNumber)) pPushNumber = nullptr;
}

// ============================================================
// DivxDecoder forwarding diagnostics
// ============================================================
// This DLL's real job (see "MANDATORY PROXY EXPORTS" at the top) is to
// pose as DivxDecoder.dll so WoW.exe loads it, then transparently
// forward the actual Divx codec calls to DivxDecoder_org.dll (the real
// decoder, renamed) via linker-level export forwarding -- pure PE
// forwarding, so none of our own code runs on the actual decode calls
// and we can't log them directly. What we CAN do is verify, at load
// time, that DivxDecoder_org.dll actually loads from next to us and
// that every function name we forward really exists on it.
//
// NOTE: cinematics triggered from the glue/login screen (expansion
// intro movies, the "Cinematics" replay button) were confirmed broken
// even with the untouched, unmodified DivxDecoder_org.dll swapped in
// directly (no proxy at all) -- so that specific issue is NOT caused by
// this DLL. Left this diagnostic in place since it's still useful for
// catching any future forwarding breakage for the in-world cinematics
// path, which this DLL IS responsible for.
static void VerifyDivxForwarding() {
    char modPath[MAX_PATH] = {};
    if (g_hSelfModule) GetModuleFileNameA(g_hSelfModule, modPath, MAX_PATH);
    char* lastSlash = strrchr(modPath, '\\');
    if (lastSlash) *(lastSlash + 1) = '\0'; else modPath[0] = '\0';
    char orgPath[MAX_PATH] = {};
    strncpy(orgPath, modPath, sizeof(orgPath) - 1);
    strncat(orgPath, "DivxDecoder_org.dll", sizeof(orgPath) - strlen(orgPath) - 1);

    HMODULE hOrg = GetModuleHandleA("DivxDecoder_org.dll");
    bool alreadyLoaded = (hOrg != nullptr);
    if (!hOrg) hOrg = LoadLibraryA(orgPath);

    if (!hOrg) {
        DbgLog("VerifyDivxForwarding: FAILED to load \"%s\" (GetLastError=%lu)",
               orgPath, GetLastError());
        return;
    }
    DbgLog("VerifyDivxForwarding: DivxDecoder_org.dll loaded OK from \"%s\" (was already loaded=%s, hModule=%p)",
           orgPath, alreadyLoaded ? "yes" : "no", (void*)hOrg);

    static const char* names[] = {
        "DivxDecode", "SetOutputFormat", "InitializeDivxDecoder", "UnInitializeDivxDecoder"
    };
    int okCount = 0, missingCount = 0;
    for (int i = 0; i < (int)(sizeof(names) / sizeof(names[0])); i++) {
        FARPROC p = GetProcAddress(hOrg, names[i]);
        if (p) {
            okCount++;
        } else {
            missingCount++;
            DbgLog("VerifyDivxForwarding: MISSING export \"%s\" on DivxDecoder_org.dll -- forward for this name is dead", names[i]);
        }
    }
    DbgLog("VerifyDivxForwarding: done, %d/%d forwarded names resolve on the real DLL (missing=%d)",
           okCount, (int)(sizeof(names) / sizeof(names[0])), missingCount);

    if (!alreadyLoaded) FreeLibrary(hOrg);
}

// ============================================================
// DLL entry point
// ============================================================
BOOL APIENTRY DllMain(HMODULE h, DWORD r, LPVOID) {
    if (r == DLL_PROCESS_ATTACH) {
        DisableThreadLibraryCalls(h);
        InitializeCriticalSection(&g_monitorLock);
        InitializeCriticalSection(&g_logLock);
        g_logLockInit = true;
        g_hSelfModule = h;
        DbgLog("DLL_PROCESS_ATTACH - DivxDecoder proxy loaded");
        VerifyDivxForwarding();
        LoadSavedResolutions();
        LoadSavedMonitorSelection();
        // Correct Config.wtf's gxResolution CVar to match the saved
        // monitor's native size BEFORE Wow.exe's own startup code reads
        // this file -- see PatchConfigResolutionForSavedMonitor for why
        // this eliminates the visible "wrong resolution for a couple
        // seconds" delay at launch instead of trying to fix it up at
        // runtime after the window/device already exists.
        PatchConfigResolutionForSavedMonitor();
        InstallCreateWindowHook();
        CreateThread(0, 0, MainThread, 0, 0, 0);
    }
    if (r == DLL_PROCESS_DETACH) {
        g_running = false;
        DbgLog("DLL_PROCESS_DETACH");
        if (g_origCreateWindowExA) PatchExeIatEntry("CreateWindowExA", (void*)g_origCreateWindowExA);
        if (g_origCreateWindowExW) PatchExeIatEntry("CreateWindowExW", (void*)g_origCreateWindowExW);
        if (g_origWndProc) {
            HWND wowWnd = FindWowWindow();
            if (wowWnd) SetWindowLongPtrA(wowWnd, GWLP_WNDPROC, (LONG_PTR)g_origWndProc);
        }
        DeleteCriticalSection(&g_monitorLock);
        g_logLockInit = false;
        DeleteCriticalSection(&g_logLock);
    }
    return TRUE;
}
