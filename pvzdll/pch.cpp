#include "pch.h"
#include "../pvzclass/Creators.h"
#include <map>
#include <vector>
#include <fstream>
#include <sstream>
#include <string>
#include <array>
#include <set>
#include <set>
#include <cstdlib>
#include <algorithm>
#include <cmath>
#include <cstdarg>

// pch.cpp: 与预编译头对应的源文件

// ==================== 崩溃诊断 / 防崩溃加固 ====================
// 背景：游戏偶发崩溃（报告里只有"崩溃地址 0x58CD5F45"这类模块基址+RVA，无法反查）。
// 本模块做四件事：
//   ① 进游戏时把**全部已加载模块**的 基址/大小/名称 落盘 → 任何崩溃地址都能查出
//      属于哪个模块、RVA 是多少（配合 Release\pvzdll.map 可直接定位到函数名）。
//   ② 登记每一个 hook trampoline（VirtualAlloc 出来的 4KB RWX 页）的基址/来源函数/行号
//      → 若崩溃落在 trampoline 里，能直接说出是哪个 hook。
//   ③ 装 VEH（Vectored Exception Handler）：崩溃时把 异常码/崩溃地址/所属模块+RVA/
//      全部寄存器/栈内容/EBP 回溯/最后执行步骤 写进 D:\pvz_crash.log，
//      然后返回 CONTINUE_SEARCH 交还给游戏原有处理链（不干扰 PVZ防崩溃程序）。
//   ④ 给每帧主循环 + 绘制回调套 __try 外壳：记录现场后吞掉异常，只跳这一帧，游戏不死。
//
// ★★ 铁律（与本文件既有"崩溃铁律"一致）：异常处理器内**只用 Win32 API**，
//    禁止 CRT（fopen/printf/new/std::map/std::string）—— 崩溃时 CRT 堆锁可能已被持有。
#include <windows.h>
#include <tlhelp32.h>

#define CRASH_MAX_MODULES 128
#define CRASH_MAX_TRAMPS  96
#define CRASH_LOG_PATH    "D:\\pvz_crash.log"

struct CrashModule { DWORD base; DWORD size; char name[64]; };
static CrashModule  g_crashModules[CRASH_MAX_MODULES];
static int          g_crashModuleCount = 0;

struct CrashTramp { DWORD base; DWORD size; const char* func; int line; };
static CrashTramp   g_crashTramps[CRASH_MAX_TRAMPS];
static int          g_crashTrampCount = 0;

// 每帧各段开头用 CRASH_STEP 打点，崩溃时能看到最后进入的是哪一段
static const char*  g_crashStep = "startup";
static int          g_crashStepLine = 0;
#define CRASH_STEP(x) do { g_crashStep = (x); g_crashStepLine = __LINE__; } while (0)

// 崩溃日志预算（防止异常风暴把磁盘写满 / 递归刷屏）
static volatile LONG g_crashLogBudget = 24;

// ---- trampoline 分配（替代裸 VirtualAlloc，带登记）----
static int AllocTramp(const char* func, int line)
{
	// 注意：这里必须是原始 VirtualAlloc，不能走 TRAMPOLINE_ALLOC 宏（否则无限递归）
	void* p = VirtualAlloc(NULL, 4096, MEM_COMMIT, PAGE_EXECUTE_READWRITE);
	if (p == NULL) return 0;
	if (g_crashTrampCount < CRASH_MAX_TRAMPS)
	{
		CrashTramp& t = g_crashTramps[g_crashTrampCount++];
		t.base = (DWORD)p;
		t.size = 4096;
		t.func = func;
		t.line = line;
	}
	return (int)p;
}
#define TRAMPOLINE_ALLOC() AllocTramp(__FUNCTION__, __LINE__)

// ---- 地址可读性检查（跨页递归，纯 Win32）----
static bool CrashIsReadable(DWORD addr, DWORD len)
{
	if (addr < 0x10000 || len == 0) return false;
	MEMORY_BASIC_INFORMATION mbi;
	if (VirtualQuery((const void*)addr, &mbi, sizeof(mbi)) == 0) return false;
	if (mbi.State != MEM_COMMIT) return false;
	if (mbi.Protect & PAGE_GUARD) return false;
	if ((mbi.Protect & 0xFF) == PAGE_NOACCESS) return false;
	DWORD regionBase = (DWORD)mbi.BaseAddress;
	DWORD regionEnd = regionBase + (DWORD)mbi.RegionSize;
	if (addr < regionBase) return false;
	if (regionEnd <= addr) return false;          // RegionSize 为 0 等异常情形，防无限递归
	if (addr + len <= regionEnd) return true;
	return CrashIsReadable(regionEnd, addr + len - regionEnd);
}

// ---- 极简日志输出（无 CRT）----
// ★★ 2026-10-16 改动：日志句柄**只开一次并常驻**。
//   原因（重要）：本 VEH 会在"堆函数内部崩溃"时被调用，此时 CRT/进程堆锁**很可能已被
//   本线程持有且堆状态不一致**。原来每次写日志都 CreateFileA —— 它会走 KERNELBASE 的
//   路径解析并**在进程堆上分配内存** → 在当前线程里**重入那个已经不一致的堆**
//   → 二次损坏/二次 AV（日志里 frames 链上 ntdll 帧重复出现就是这个特征），
//   把一次"本来能活的堆损坏"放大成硬崩。
//   常驻句柄后，异常处理器里只剩 WriteFile（内核态分配，不碰进程堆），安全得多。
//   共享模式带 FILE_SHARE_WRITE，保证 S6 那份 DLL 仍能自己打开同一个日志文件。
static HANDLE g_crashLogHandle = INVALID_HANDLE_VALUE;
static volatile LONG g_inExceptionHandler = 0;   // >0 = 正在异常处理器里（禁止任何会分配堆的调用）
static void CrashLogEnsureHandle()
{
	if (g_crashLogHandle != INVALID_HANDLE_VALUE) return;
	g_crashLogHandle = CreateFileA(CRASH_LOG_PATH, FILE_APPEND_DATA,
		FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, NULL,
		OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
}
static void CrashWriteRaw(const char* s, int len)
{
	if (len <= 0) return;
	if (g_crashLogHandle == INVALID_HANDLE_VALUE)
	{
		// ★ 异常处理器里**绝不** CreateFileA（它会分配进程堆，重入已被损坏/加锁的堆）。
		//   正常流程由 init() 预先开好句柄。
		if (g_inExceptionHandler) return;
		CrashLogEnsureHandle();
		if (g_crashLogHandle == INVALID_HANDLE_VALUE) return;
	}
	DWORD written = 0;
	if (!WriteFile(g_crashLogHandle, s, (DWORD)len, &written, NULL))
	{
		// 句柄失效（文件被外部工具删除/独占）：关掉，下次尝试重开一次
		CloseHandle(g_crashLogHandle);
		g_crashLogHandle = INVALID_HANDLE_VALUE;
	}
}
static void CrashStr(const char* s)
{
	int n = 0; while (s[n]) n++;
	CrashWriteRaw(s, n);
}
static void CrashHex8(char* out, DWORD v)
{
	static const char digits[] = "0123456789ABCDEF";
	for (int i = 7; i >= 0; i--) { out[i] = digits[v & 0xF]; v >>= 4; }
}
// 形如 "label=0x1234ABCD\r\n"
static void CrashLineHex(const char* label, DWORD v)
{
	char buf[160]; int p = 0;
	for (const char* L = label; *L && p < 100; ++L) buf[p++] = *L;
	buf[p++] = '='; buf[p++] = '0'; buf[p++] = 'x';
	CrashHex8(buf + p, v); p += 8;
	buf[p++] = '\r'; buf[p++] = '\n';
	CrashWriteRaw(buf, p);
}
// 形如 "label=0x1234ABCD module=xxx.dll rva=0x00005F45 [TRAMPOLINE off=0x.. from Func@line]\r\n"
static void CrashLineAddr(const char* label, DWORD addr)
{
	char buf[384]; int p = 0;
	for (const char* L = label; *L && p < 100; ++L) buf[p++] = *L;
	buf[p++] = '='; buf[p++] = '0'; buf[p++] = 'x';
	CrashHex8(buf + p, addr); p += 8;

	const char* modName = "?";
	DWORD rva = addr;
	for (int i = 0; i < g_crashModuleCount; i++)
	{
		if (addr >= g_crashModules[i].base &&
			addr < g_crashModules[i].base + g_crashModules[i].size)
		{
			modName = g_crashModules[i].name;
			rva = addr - g_crashModules[i].base;
			break;
		}
	}
	const char* s = " module=";
	for (; *s && p < 330; ++s) buf[p++] = *s;
	for (const char* L = modName; *L && p < 340; ++L) buf[p++] = *L;
	s = " rva=0x";
	for (; *s && p < 350; ++s) buf[p++] = *s;
	CrashHex8(buf + p, rva); p += 8;

	for (int i = 0; i < g_crashTrampCount; i++)
	{
		if (addr >= g_crashTramps[i].base &&
			addr < g_crashTramps[i].base + g_crashTramps[i].size)
		{
			s = " [TRAMPOLINE off=0x";
			for (; *s && p < 350; ++s) buf[p++] = *s;
			CrashHex8(buf + p, addr - g_crashTramps[i].base); p += 8;
			s = " from ";
			for (; *s && p < 360; ++s) buf[p++] = *s;
			for (const char* L = (g_crashTramps[i].func ? g_crashTramps[i].func : "?"); *L && p < 375; ++L) buf[p++] = *L;
			break;
		}
	}
	buf[p++] = '\r'; buf[p++] = '\n';
	if (p > (int)sizeof(buf)) p = (int)sizeof(buf);
	CrashWriteRaw(buf, p);
}

// 只记录"真崩溃"，跳过调试器断点/单步/线程改名等良性异常
// （否则预算会被良性异常耗光，真崩溃反而没记上）
static bool CrashIsFatalCode(DWORD c)
{
	switch (c)
	{
	case 0xC0000005: return true;   // Access violation
	case 0xC000001D: return true;   // Illegal instruction
	case 0xC0000094: return true;   // Integer divide by zero
	case 0xC0000095: return true;   // Integer overflow
	case 0xC0000096: return true;   // Privileged instruction
	case 0xC00000FD: return true;   // Stack overflow
	case 0xC0000374: return true;   // Heap corruption
	case 0xC0000409: return true;   // Stack buffer overrun (/GS)
	case 0xE06D7363: return true;   // C++ exception（std::stof/stoi 抛出且无人接住时致命）
	default: return false;
	}
}

// ---- 写一份完整崩溃现场 ----
static void CrashSnapshotModules();   // 前向声明（定义在下方；崩溃时可能需实时重取）
// 地址是否落在"已快照的模块表"里
static bool CrashAddrInModule(DWORD addr)
{
	for (int i = 0; i < g_crashModuleCount; i++)
		if (addr >= g_crashModules[i].base && addr < g_crashModules[i].base + g_crashModules[i].size)
			return true;
	return false;
}
// 是否落在 ntdll / KERNELBASE 内：这些地方崩溃时堆锁可能已被持有，
// 不能在异常处理器里再跑会分配内存的 API（CreateToolhelp32Snapshot）。
static bool CrashAddrIsSystemHeap(DWORD addr)
{
	for (int i = 0; i < g_crashModuleCount; i++)
	{
		const char* n = g_crashModules[i].name;
		bool sys = false;
		const char* k1 = "ntdll"; const char* k2 = "KERNELBASE";
		int j = 0; while (k1[j] && n[j] == k1[j]) j++; if (!k1[j]) sys = true;
		j = 0; while (k2[j] && n[j] == k2[j]) j++; if (!k2[j]) sys = true;
		if (!sys) continue;
		if (addr >= g_crashModules[i].base && addr < g_crashModules[i].base + g_crashModules[i].size)
			return true;
	}
	return false;
}
static void CrashDumpModules()
{
	CrashStr("modules(at crash):\r\n");
	for (int i = 0; i < g_crashModuleCount; i++)
	{
		char buf[160]; int p = 0;
		const char* s = "  base=0x";
		for (; *s; ++s) buf[p++] = *s;
		CrashHex8(buf + p, g_crashModules[i].base); p += 8;
		s = " end=0x";
		for (; *s; ++s) buf[p++] = *s;
		CrashHex8(buf + p, g_crashModules[i].base + g_crashModules[i].size); p += 8;
		buf[p++] = ' ';
		for (const char* L = g_crashModules[i].name; *L && p < 150; ++L) buf[p++] = *L;
		buf[p++] = '\r'; buf[p++] = '\n';
		CrashWriteRaw(buf, p);
	}
}

static void CrashLogException(EXCEPTION_POINTERS* ep, const char* kind)
{
	DWORD code = 0, addr = 0, fault = 0;
	if (ep && ep->ExceptionRecord)
	{
		code = ep->ExceptionRecord->ExceptionCode;
		addr = (DWORD)ep->ExceptionRecord->ExceptionAddress;
		if (ep->ExceptionRecord->NumberParameters >= 2 &&
			(code == 0xC0000005 || code == 0xC0000096))
			fault = (DWORD)ep->ExceptionRecord->ExceptionInformation[1];
	}
	// ★ 2026-10-03：崩溃地址不在 INIT 快照的模块表里（例如历史报告里的
	//   0x6F6DAE77 一直查不到归属）→ 大概率是"进关卡之后才加载"的模块。
	//   此时实时重取一次模块表再写日志，后续日志就能解析出它是谁。
	//   安全门：崩溃点落在 ntdll/KERNELBASE（堆锁可能已持有）时不敢跑
	//   CreateToolhelp32Snapshot（内部会分配内存，可能二次崩溃/死锁），只 dump 旧表。
	bool unknown = !CrashAddrInModule(addr) || (fault != 0 && !CrashAddrInModule(fault));
	if (unknown && !CrashAddrIsSystemHeap(addr) && !CrashAddrIsSystemHeap(fault))
		CrashSnapshotModules();
	CrashStr("\r\n==== PVZ CRASH (");
	CrashStr(kind ? kind : "?");
	CrashStr(") ====\r\n");
	CrashLineHex("code", code);
	CrashLineAddr("eip", addr);
	if (fault) { CrashStr("  ^ access violation at -> "); CrashLineAddr("fault", fault); }
	else CrashLineAddr("fault", fault);
	// EIP 附近代码字节（可读时 dump 16 字节）：识别 hook 字节是否被外部程序（修改器）改写
	if (addr >= 0x10000 && CrashIsReadable(addr, 16))
	{
		char cb[120]; int cp = 0;
		const char* s0 = "code@eip=";
		for (; *s0 && cp < 30; ++s0) cb[cp++] = *s0;
		static const char hx[] = "0123456789ABCDEF";
		for (int i = 0; i < 16 && cp < 110; i++)
		{
			unsigned char b = *(volatile unsigned char*)(addr + i);
			cb[cp++] = hx[b >> 4];
			cb[cp++] = hx[b & 0xF];
			cb[cp++] = ' ';
		}
		cb[cp++] = '\r'; cb[cp++] = '\n';
		CrashWriteRaw(cb, cp);
	}
	CrashStr("step=");
	CrashStr(g_crashStep ? g_crashStep : "?");
	CrashStr("\r\n");
	CrashLineHex("stepLine", (DWORD)g_crashStepLine);

	PCONTEXT ctx = ep ? ep->ContextRecord : NULL;
	if (ctx)
	{
		CrashLineHex("eax", ctx->Eax);
		CrashLineHex("ebx", ctx->Ebx);
		CrashLineHex("ecx", ctx->Ecx);
		CrashLineHex("edx", ctx->Edx);
		CrashLineHex("esi", ctx->Esi);
		CrashLineHex("edi", ctx->Edi);
		CrashLineHex("ebp", ctx->Ebp);
		CrashLineHex("esp", ctx->Esp);

		CrashStr("stack(top 40 dwords):\r\n");
		DWORD sp = ctx->Esp & ~3u;
		for (int i = 0; i < 40; i++)
		{
			DWORD a = sp + (DWORD)i * 4;
			if (!CrashIsReadable(a, 4)) break;
			DWORD v = *(volatile DWORD*)a;
			CrashLineAddr("  sp", v);
		}

		CrashStr("frames(ebp chain):\r\n");
		DWORD ebp = ctx->Ebp & ~3u;
		for (int i = 0; i < 32; i++)
		{
			if (!CrashIsReadable(ebp, 8)) break;
			DWORD ret = *(volatile DWORD*)(ebp + 4);
			DWORD next = *(volatile DWORD*)ebp;
			CrashLineAddr("  ret", ret);
			if (next <= ebp || !CrashIsReadable(next, 8)) break;
			ebp = next;
		}
	}
	// trampoline 表（崩溃地址若不在表里，也能据此判断它落在哪两个 trampoline 之间）
	CrashStr("trampolines:\r\n");
	for (int i = 0; i < g_crashTrampCount; i++)
	{
		char buf[256]; int p = 0;
		const char* s = "  tramp base=0x";
		for (; *s; ++s) buf[p++] = *s;
		CrashHex8(buf + p, g_crashTramps[i].base); p += 8;
		s = " end=0x";
		for (; *s; ++s) buf[p++] = *s;
		CrashHex8(buf + p, g_crashTramps[i].base + g_crashTramps[i].size); p += 8;
		s = " from ";
		for (; *s && p < 200; ++s) buf[p++] = *s;
		for (const char* L = (g_crashTramps[i].func ? g_crashTramps[i].func : "?"); *L && p < 240; ++L) buf[p++] = *L;
		buf[p++] = '\r'; buf[p++] = '\n';
		CrashWriteRaw(buf, p);
	}
	// 崩溃地址无法归属到任何模块 → 把（刚刷新的）整表写进日志，便于事后反查
	// 0x6F6xxxxx / 0x69xxxxxx 这类"只在运行期出现"的地址。
	if (unknown)
		CrashDumpModules();
	CrashStr("==== PVZ CRASH END ====\r\n");
}

// VEH：只记录，绝不改变游戏原有异常处理流程（游戏自身的 SEH / PVZ防崩溃程序照常接管）
static LONG CALLBACK CrashVEH(PEXCEPTION_POINTERS ep)
{
	DWORD code = (ep && ep->ExceptionRecord) ? ep->ExceptionRecord->ExceptionCode : 0;
	if (!CrashIsFatalCode(code)) return EXCEPTION_CONTINUE_SEARCH;
	if (InterlockedDecrement(&g_crashLogBudget) < 0)
	{
		InterlockedIncrement(&g_crashLogBudget);   // 预算耗尽，不再写盘
		return EXCEPTION_CONTINUE_SEARCH;
	}
	// ★ 进入"异常处理器"模式：期间禁止 CreateFileA / CreateToolhelp32Snapshot 等
	//   任何会在进程堆上分配内存的调用（堆锁可能已被本线程持有且状态不一致）。
	InterlockedIncrement(&g_inExceptionHandler);
	CrashLogException(ep, "VEH");
	InterlockedDecrement(&g_inExceptionHandler);
	return EXCEPTION_CONTINUE_SEARCH;
}

// __except 过滤函数：记录后吞掉异常（用于每帧轮询 / 绘制回调外壳）
static LONG CrashSwallowFilter(EXCEPTION_POINTERS* ep)
{
	DWORD code = (ep && ep->ExceptionRecord) ? ep->ExceptionRecord->ExceptionCode : 0;
	if (!CrashIsFatalCode(code)) return EXCEPTION_EXECUTE_HANDLER;   // 良性异常：静默吞掉
	if (InterlockedDecrement(&g_crashLogBudget) >= 0)
		CrashLogException(ep, "SWALLOW");
	return EXCEPTION_EXECUTE_HANDLER;
}

// ==================== 安全内存访问守卫（2026-10-03 新增）====================
// 背景：本 DLL 全部游戏内存访问都走 PVZClass 的 Memory::ReadMemory/WriteMemory。
//   它们在 localExecute（DLL 注入）分支里是**裸解引用**：
//       T* buffer = (T*)address;  return *buffer;        // 读
//       AllAccess(address); *(T*)address = value;        // 写
//   于是：
//     · 读一个野地址 → 直接 AV 崩溃（实证：D:\pvz_crash.log 里 mod 自身崩溃点
//       "icemelon:shot" → movss xmm0,[edi] 而 edi=0x5C；"gatling:ult" →
//       mov [eax+0x5568] 而 eax=0x02BC9F40 是已释放的 Board）；
//     · **写**一个野地址不会崩（堆页可写）→ 直接改坏任意内存，包括 CRT 堆
//       → 之后 ntdll 堆遍历崩溃 / 游戏对象指针变野 / 行为异常（症状随机难复现）。
//   这两类失败模式与实测症状（ntdll rva 0x3C486/0x52A6F 堆代码内崩溃、
//   0x46441F 游戏对象指针指向栈地址）完全吻合，故在此加一道守卫。
//
// 守卫做两件事：
//   ① 读写前校验目标区间已提交、可读 / 可写（VirtualQuery + 16 项区域缓存）；
//      校验不过：读返回 0、写直接丢弃 —— 绝不触碰无效内存。
//   ② 每次拦截把 地址 / 长度 / 方向 / 当前 CRASH_STEP 打点 追加进
//      D:\pvz_crash.log（同一地址只记一次，上限 64 条）→ 可直接反查调用点。
// ★ 只拦"非法地址"；合法地址行为与原来逐字节一致（写仍走 AllAccess 解锁页保护）。
// ★ 守卫本身只用 Win32 API（VirtualQuery/CreateFileA/WriteFile），无 CRT，hook 内可用。
#define MEMGUARD_REGIONS 16
struct MemGuardRegion { DWORD lo; DWORD hi; };
static MemGuardRegion g_memGuardCache[MEMGUARD_REGIONS];
static int           g_memGuardCacheNext = 0;
static DWORD         g_memGuardLogged[64];
static int           g_memGuardLoggedCount = 0;
static int           g_memGuardHitCount = 0;   // 累计拦截次数（未打点的也算）

static bool MemGuardOk(DWORD addr, DWORD len)
{
	if (len == 0) len = 1;
	if (addr < 0x10000) return false;                 // 空指针/低位野指针
	DWORD hi = addr + len;
	if (hi < addr) return false;                      // 溢出
	for (int i = 0; i < MEMGUARD_REGIONS; i++)        // 缓存命中：两次比较
		if (addr >= g_memGuardCache[i].lo && hi <= g_memGuardCache[i].hi)
			return true;
	MEMORY_BASIC_INFORMATION mbi;
	if (VirtualQuery((const void*)addr, &mbi, sizeof(mbi)) == 0) return false;
	if (mbi.State != MEM_COMMIT) return false;
	if (mbi.Protect & PAGE_GUARD) return false;
	DWORD prot = mbi.Protect & 0xFF;
	// 只拦"一定会 AV"的页：未提交 / NOACCESS / GUARD。
	// ★ 不额外收紧（例如不拒绝 PAGE_EXECUTE）——守卫的目标是"比裸解引用更安全"，
	//   而不是改变合法访问的行为，否则会把原本能用的读写误拦成静默失效。
	if (prot == PAGE_NOACCESS || prot == 0) return false;
	DWORD rlo = (DWORD)mbi.BaseAddress;
	DWORD rhi = rlo + (DWORD)mbi.RegionSize;
	if (rhi <= rlo) return false;
	if (hi > rhi) return false;                       // 跨区域：保守拒绝（访问长度都很小）
	g_memGuardCache[g_memGuardCacheNext] = { rlo, rhi };
	g_memGuardCacheNext = (g_memGuardCacheNext + 1) % MEMGUARD_REGIONS;
	return true;
}

static void MemGuardLog(DWORD addr, DWORD len, char kind)
{
	g_memGuardHitCount++;
	for (int i = 0; i < g_memGuardLoggedCount; i++)
		if (g_memGuardLogged[i] == addr) return;      // 同一地址只记一次，防刷屏
	if (g_memGuardLoggedCount < 64) g_memGuardLogged[g_memGuardLoggedCount++] = addr;
	CrashStr("\r\n---- MEMGUARD blocked ");
	CrashStr(kind == 'R' ? "READ" : "WRITE");
	CrashStr(" ----\r\n");
	CrashLineAddr("addr", addr);
	CrashLineHex("len", len);
	CrashStr("step="); CrashStr(g_crashStep ? g_crashStep : "?");
	CrashStr("\r\n");
	CrashLineHex("stepLine", (DWORD)g_crashStepLine);
}

template <class T>
static T MemSafeRead(DWORD address)
{
	if (!MemGuardOk(address, (DWORD)sizeof(T)))
	{
		MemGuardLog(address, (DWORD)sizeof(T), 'R');
		return (T)0;
	}
	return PVZ::Memory::ReadMemory<T>(address);
}

template <class T>
static BOOL MemSafeWrite(DWORD address, T value)
{
	if (!MemGuardOk(address, (DWORD)sizeof(T)))
	{
		MemGuardLog(address, (DWORD)sizeof(T), 'W');
		return FALSE;
	}
	return PVZ::Memory::WriteMemory<T>(address, value);
}

// ==================== 堆完整性看门狗（2026-10-16 新增）====================
// 背景：本项目"堆被越界写坏"的崩溃，症状全都是**写坏之后很久**才在 ntdll 堆函数里
//   fault=0 随机崩（现场与 mod 毫无关系），因此极难定位，只能靠猜。
// 这道看门狗把"发现"提前到**第一次坏掉的那一帧**：
//   · 每 HEAPWATCH_INTERVAL 帧调一次 HeapValidate(GetProcessHeap(), 0, NULL)：只读遍历，
//     不分配内存、不碰 CRT，坏堆返回 FALSE；
//   · 一旦由"好"变"坏"，立刻写一条 `---- HEAPWATCH first corruption ----`（含帧号 + 当时
//     最后经过的 step/stepLine），并且**只记一次**（之后不再扫坏堆）。
// 判读：
//   · 日志里**没有** HEAPWATCH 段 ⇒ 这一局没发生堆损坏（说明修复有效 / 或问题不在这条路径）；
//   · 有 ⇒ 损坏发生在"该帧号之前的那一小段帧里" ⇒ 用 ini 开关二分（关掉某个机制看还崩不崩）
//     就能把范围缩到一个模块；配合 PageHeap（见《崩溃修复说明》）可精确到一条指令。
// ★ HeapValidate 要遍历整个堆（毫秒级），所以默认间隔 600 帧；找到问题后用
//   plant_mechanics.ini 的 HEAPWATCH=0 关掉（零开销）。
static int  g_heapWatchOn = 1;          // ini: HEAPWATCH（1=开，0=关）
static int  g_heapWatchCounter = 0;
static int  g_heapWatchFrames = 0;
static int  g_heapWatchFailStreak = 0;
static bool g_heapWatchQuit = false;
#define HEAPWATCH_INTERVAL 600

// 只在 onGameObjectsUpdate 帧首调用：此时 g_crashStep 还是**上一帧**结束时的标记
static void HeapWatchTick()
{
	if (!g_heapWatchOn || g_heapWatchQuit) return;
	g_heapWatchFrames++;
	if (++g_heapWatchCounter < HEAPWATCH_INTERVAL) return;
	g_heapWatchCounter = 0;
	BOOL ok = TRUE;
	__try { ok = HeapValidate(GetProcessHeap(), 0, NULL); }
	__except (EXCEPTION_EXECUTE_HANDLER) { ok = FALSE; }
	if (ok)
	{
		g_heapWatchFailStreak = 0;
		return;
	}
	// ★ 连续两次失败才算数：另一个线程（音频等）正好在操作堆时，单次 HeapValidate
	//   可能看到瞬时不一致而误报；连续两次（间隔 HEAPWATCH_INTERVAL 帧）就基本确定是真损坏。
	if (++g_heapWatchFailStreak < 2) return;
	g_heapWatchQuit = true;
	CrashStr("\r\n---- HEAPWATCH first corruption ----\r\n");
	CrashLineHex("frameOfModFrameStart", (DWORD)g_heapWatchFrames);
	CrashStr("stepAtPreviousFrameEnd=");
	CrashStr(g_crashStep ? g_crashStep : "?");
	CrashStr("\r\n");
	CrashLineHex("stepLine", (DWORD)g_crashStepLine);
	CrashStr("hint: the corrupting write happened before this frame;\r\n");
	CrashStr("hint: bisect with plant_mechanics.ini switches (or use PageHeap)\r\n");
}

// ---- 模块表快照（进游戏时跑一次，崩溃时只做静态查表，安全）----
static void CrashSnapshotModules()
{
	g_crashModuleCount = 0;
	HANDLE snap = CreateToolhelp32Snapshot(TH32CS_SNAPMODULE, GetCurrentProcessId());
	if (snap == INVALID_HANDLE_VALUE) return;
	MODULEENTRY32W me;
	me.dwSize = sizeof(me);
	if (Module32FirstW(snap, &me))
	{
		do {
			if (g_crashModuleCount >= CRASH_MAX_MODULES) break;
			CrashModule& m = g_crashModules[g_crashModuleCount++];
			m.base = (DWORD)me.modBaseAddr;
			m.size = me.modBaseSize;
			int i = 0;
			for (; i < 63 && me.szModule[i]; i++)
			{
				wchar_t w = me.szModule[i];
				m.name[i] = (w < 128) ? (char)w : '?';
			}
			m.name[i] = 0;
		} while (Module32NextW(snap, &me));
	}
	CloseHandle(snap);
}

static void InstallCrashHandler()
{
	CrashStr("\r\n================ PVZ DLL INIT ================\r\n");
	CrashSnapshotModules();
	for (int i = 0; i < g_crashModuleCount; i++)
	{
		char buf[256]; int p = 0;
		const char* s = "mod base=0x";
		for (; *s; ++s) buf[p++] = *s;
		CrashHex8(buf + p, g_crashModules[i].base); p += 8;
		s = " end=0x";
		for (; *s; ++s) buf[p++] = *s;
		CrashHex8(buf + p, g_crashModules[i].base + g_crashModules[i].size); p += 8;
		s = " ";
		for (; *s; ++s) buf[p++] = *s;
		for (const char* L = g_crashModules[i].name; *L && p < 240; ++L) buf[p++] = *L;
		buf[p++] = '\r'; buf[p++] = '\n';
		CrashWriteRaw(buf, p);
	}
	CrashStr("================ INIT END ================\r\n");
	AddVectoredExceptionHandler(1, CrashVEH);
}

// ---- hook 站点看门狗（修改器共存，2026-09-08）----
// 背景：PVZTools 等修改器也 hook 同一批游戏函数。实测崩溃 EIP=0x13C70FFF 恰为
// 某次会话中 InstallFlowerPotHook 的 trampoline 页尾（tramp base=0x13C70000 end=0x13C71000，
// D:\pvz_crash.log trampoline 表实证）——游戏执行 trampoline 时跳飞到拷贝字节之外。
// 看门狗每 2 秒巡检各站点：应仍是我们写的 E9 且目标落在某个 trampoline 页内。
// 被修改器事后改写/接管 → 留痕一次（HOOKCLOBBER），功能静默失效但游戏稳定；
// 不做自动重装（避免与修改器互相无限覆盖）。
struct HookWatchRec { DWORD site; const char* name; int state; };   // state 0=未装 1=在位 2=被夺(已留痕)
static HookWatchRec g_hookWatch[] = {
	{0x40E020, "CanPlantAt", 0},       {0x45F1E0, "KernelpultButter", 0},
	{0x40E760, "ExpPouchMouseMove", 0},{0x416880, "ExpPouchHighlight", 0},
	{0x411F20, "ExpPouchMouse", 0},    {0x41AA40, "ExpPouchDraw", 0},
	{0x46E6C7, "IcicleImage", 0},      {0x46E805, "PeaColor", 0},
	{0x46340B, "Blover", 0},           {0x453A90, "AwardSeed", 0},
	{0x453C17, "Unlock", 0},           {0x417DA0, "ExpTextDraw", 0},
	{0x45F874, "StarVolley", 0},       {0x4606B7, "Torchwood1", 0},
	{0x4606CB, "Torchwood2", 0},       {0x45FB1D, "MarigoldProduce", 0},
	{0x464C1C, "Cabbage", 0},          {0x464B32, "SplitPea", 0},
	{0x461447, "BlastChomper", 0},     {0x463920, "BlastGuard", 0},
	{0x461490, "BlastSkipAnim", 0},    {0x4614D7, "BlastSkipCall", 0},
	{0x4620BD, "BlastMagnet", 0},      {0x46143C, "BlastFind", 0},
	{0x5317C0, "BlastDmg1", 0},        {0x5312D0, "BlastDmg2", 0},
	{0x532B70, "BlastBurn", 0},        {0x52B9D1, "HypnoShroom", 0},
	{0x463ED2, "PlantFreedTail", 0},
};
static void HookSiteWatchdog()
{
	static DWORD s_last = 0;
	DWORD now = GetTickCount();
	if (s_last != 0 && now - s_last < 2000)
		return;
	s_last = now;
	for (int i = 0; i < (int)(sizeof(g_hookWatch) / sizeof(g_hookWatch[0])); i++)
	{
		HookWatchRec& r = g_hookWatch[i];
		if (r.state == 2)
			continue;
		if (!CrashIsReadable(r.site, 5))
			continue;
		bool ours = false;
		if (MemSafeRead<BYTE>(r.site) == 0xE9)
		{
			DWORD dest = r.site + 5 + (DWORD)MemSafeRead<int>(r.site + 1);
			for (int t = 0; t < g_crashTrampCount && !ours; t++)
				if (dest >= g_crashTramps[t].base && dest < g_crashTramps[t].base + g_crashTramps[t].size)
					ours = true;
		}
		if (ours)
		{
			if (r.state == 0)
				r.state = 1;
			continue;
		}
		if (r.state == 1)
		{
			r.state = 2;   // 曾确认在位，现在被夺走 → 留痕
			char buf[128]; int p = 0;
			const char* s = "HOOKCLOBBER name=";
			for (; *s && p < 40; ++s) buf[p++] = *s;
			for (const char* L = r.name; *L && p < 70; ++L) buf[p++] = *L;
			s = " site=0x";
			for (; *s && p < 80; ++s) buf[p++] = *s;
			CrashHex8(buf + p, r.site); p += 8;
			buf[p++] = '\r'; buf[p++] = '\n';
			CrashWriteRaw(buf, p);
		}
	}
}

// ---- 僵尸染色解锁（带字节校验，防写坏游戏代码）----
// PVZ::Animation::UnLock(AP_ZOMBIECOLOR) 会无条件向游戏代码 0x52D3EA 写 4 字节
// 0x909030EB（jmp 跳过原生"栈取色"）。0x52xxxx 是运行时解密区，一旦那 4 字节不是
// 预期的 `mov eax,[esp+30]`(8B 44 24 30)，这次写入就会把游戏代码改成 jmp+nop，
// 破坏指令边界 → 随机崩溃（代码区被重置/重新加密时最容易踩到）。
// 这里加校验：只在这两种已知形态下才写；异常形态宁可让染色失效，也绝不写坏代码。
static void SafeUnlockZombieColor()
{
	const DWORD UNLOCK_ADDR = 0x52D3EA;
	const int   LOCKED_BYTES = (int)0x3024448B;   // 8B 44 24 30 : mov eax,[esp+30]
	const int   UNLOCK_BYTES = (int)0x909030EB;   // EB 30 90 90 : jmp +0x32; nop; nop
	if (!CrashIsReadable(UNLOCK_ADDR, 4)) return;
	int cur = MemSafeRead<int>(UNLOCK_ADDR);
	if (cur == LOCKED_BYTES)
		MemSafeWrite<int>(UNLOCK_ADDR, UNLOCK_BYTES);
	// cur == UNLOCK_BYTES → 已解锁，无需重写；其它值 → 放弃写入（安全优先）
}

// 重新上锁：恢复 0x52D3EA 的原版 `mov eax,[esp+30]`（闪白诊断期让游戏原版着色代码
// 自由运行，才能捕获它对 reanim 通道的真实写入；防止上一局遗留的解锁补丁干扰）
static void SafeLockZombieColor()
{
	const DWORD UNLOCK_ADDR = 0x52D3EA;
	const int   LOCKED_BYTES = (int)0x3024448B;   // 8B 44 24 30 : mov eax,[esp+30]
	const int   UNLOCK_BYTES = (int)0x909030EB;   // EB 30 90 90 : jmp +0x32; nop; nop
	if (!CrashIsReadable(UNLOCK_ADDR, 4)) return;
	int cur = MemSafeRead<int>(UNLOCK_ADDR);
	if (cur == UNLOCK_BYTES)
		MemSafeWrite<int>(UNLOCK_ADDR, LOCKED_BYTES);
}

// ---- 僵尸 reanim 地址安全获取（绕开 PVZ::Animation 构造器的"索引陷阱"）----
// PVZ::Animation(int idoraddress) 的实现（pvzclass/Classes/Animation.cpp）：
//   if (idoraddress > 1024) BaseAddress = idoraddress;                        // 当绝对地址用
//   else BaseAddress = ReadPointer(0x6A9EC0,0x820,8,0) + idoraddress * 0xA0;  // 当作数组索引
// 而 Zombie::GetAnimation() 传进来的是 ID_INDEX(reanimId)（低 16 位索引）。
// ★ 陷阱：一旦索引 > 1024（场上 reanim 数量涨起来后必然出现），索引被当成绝对地址，
//   reanim 地址变成 1030 之类的小整数 → 后续染色/贴图操作往低地址写：
//     ① 静默失效（写到无关内存，染色/贴图不生效）
//     ② 访问违规 → 随机崩溃
//   染色、撑杆司令贴图、防爆门贴图都在 GetAnimation() 上，会同时踩这个坑。
// 这里直接按数组公式算地址并做合法性校验，异常一律返回 0（安全优先）。
// 调用方用 PVZ::Animation(reanimAddr)（传绝对地址）即可走构造器的正确分支。

// 地址是否可写（染色写 +0x48..0x54；贴图替换会整块写 0xA0）。
// 三次崩溃都是 ntdll 堆函数里的访问违规（fault=0 / 0x14 / 0xFFFFFFF8）= 堆被越界写坏，
// 所以"写之前先确认整块可写"是必要安全网（VirtualQuery 约 1μs，50 僵尸/帧开销可忽略）
static bool CrashIsWritable(DWORD addr, DWORD len)
{
	if (!CrashIsReadable(addr, len)) return false;
	MEMORY_BASIC_INFORMATION mbi;
	if (VirtualQuery((const void*)addr, &mbi, sizeof(mbi)) == 0) return false;
	DWORD p = mbi.Protect & 0xFF;
	return (p == PAGE_READWRITE || p == PAGE_EXECUTE_READWRITE ||
		p == PAGE_WRITECOPY || p == PAGE_EXECUTE_WRITECOPY);
}

static int GetZombieReanimAddr(DWORD zombieAddr)
{
	if (!zombieAddr) return 0;
	int id = MemSafeRead<int>(zombieAddr + 0x118);
	int idx = id & 0xFFFF;
	if (idx <= 0) return 0;
	if (idx > 8192) return 0;                    // 远超任何 reanim 池容量 → 必然是脏数据
	int arr = PVZ::Memory::ReadPointer(0x6A9EC0, 0x820, 8, 0);
	if (arr < 0x10000) return 0;                 // 数组基址异常（未就绪/解密前）
	int addr = arr + idx * 0xA0;
	if (addr < 0x100000) return 0;               // reanim 对象在堆上，低地址必然是错的
	if (!CrashIsWritable(addr, 0xA0)) return 0;  // ★整块必须可写（防越界写到数组外的堆内存）
	if (MemSafeRead<BYTE>(addr + 0x14)) return 0; // Animation::NotExist → 动画已移除

	return addr;
}

// 用安全地址构造 Animation（返回 false = 地址无效，调用方必须跳过）。
// ★ 不能返回 PVZ::Animation(0) 表示失败：构造器在 0 时会走 else 分支算出
//   "数组基址"（非 0！），调用方的 `if (!anim.GetBaseAddress())` 校验会失效，
//   进而把颜色/贴图写到 reanim 数组的头部 → 数据错乱。
static bool TryGetZombieReanim(DWORD zombieAddr, PVZ::Animation& outAnim)
{
	int addr = GetZombieReanimAddr(zombieAddr);
	if (!addr) return false;
	outAnim = PVZ::Animation(addr);   // addr > 0x100000（>1024）→ 走绝对地址的正确分支
	return true;
}

// ==================== reanim 轨道写入安全闸（2026-10-16）====================
// ★ 先把机制订正清楚（2026-10-16 现场反汇编核对字节，纠正了此前文档里的错误结论）：
//   · 0x472F30 FindTrackIndex **找不到轨道名时返回 0，不是 -1**
//     （结尾 `33 C0 ... ret 4`）⇒ 老文档里"idx=-1 → idx*0x60 变负数 → 写实例数组前 0x60 字节"
//     的说法**不成立**；历史上那些 `if (FindTrackIndex(name) < 0) return;` 的防护
//     **一次都没生效过**（0 不小于 0），轨道名不存在时实际是写坏了**轨道 0** 的 override。
//   · 真正会造成**堆损坏**（= 本文件一直追的那类"ntdll 里 fault=0 的随机崩"）的是：
//     把**垃圾 reanim 指针**喂给 0x473490 —— 典型来源是动画未就绪时框架返回
//     INVALID_BASEADDRESS = 0x400000（= exe 镜像基址！），而 `if (!GetBaseAddress())` 拦不住它。
//     此时 [reanim+0xC] 把 PE 头当"轨道名字表"，count 与实例数组指针全是垃圾
//     ⇒ `mov [ecx+edx+0x44], eax` 变成**任意地址写** → 堆任意位置被踩。
//   · 0x473A40（AssignRenderGroupToTrack / …Prefix）是自己遍历名字表做**前缀匹配**，
//     只对真正命中的轨道写 +0x48；同样怕垃圾 reanim（会用垃圾 count 越界写实例数组）。
// 关键陷阱：僵尸/植物的"当前动画实例"是**按动作分别建的对象**（走路/跳跃/啃咬/死亡…），
//   轨道表并不相同；对某个实例存在并不代表对另一个存在。
// ⇒ 因此**所有**轨道写入必须走 ReanimSetImageOverride（内部：reanim 必须可写堆对象 +
//   名字必须真命中 + 目标 0x60 字节可写），而不是直接 anim.SetImageOverride
//   （框架层也加了同样的闸，双保险）。
static int  ReanimTrackIndex(DWORD reanimAddr, const char* trackName);              // 定义在下方
static void ReanimSetImageOverride(DWORD reanimAddr, const char* trackName, DWORD imageAddr); // 定义在下方

// ==================== 稳健数值解析（2026-10-16）====================
// std::stoi / std::stof 在"非数字 / 超出范围"时会**抛 C++ 异常**（std::invalid_argument /
// std::out_of_range）。本项目这些解析全在 init() 的 ini 加载器里，外层没人接住
// → **ini 里一个手误就把游戏崩掉**（本文件 CrashIsFatalCode 里 0xE06D7363 那条注释说的就是这个）。
// 这里统一换成不抛版本：非法输入返回 0（与 std::stoi 成功路径行为一致），并留一行日志。
static int SafeAtoiLog(const char* s, const char* key)
{
	if (s == NULL) return 0;
	char* endp = NULL;
	long lv = strtol(s, &endp, 10);
	if (endp == s || (endp != NULL && *endp != '\0' && *endp != ' ' && *endp != '\t' && *endp != '\r'))
	{
		CrashStr("[CFG] bad integer value for key=");
		CrashStr(key ? key : "?");
		CrashStr(" raw=");
		CrashStr(s);
		CrashStr(" -> using 0\r\n");
		return 0;
	}
	if (lv > 2147483647L) lv = 2147483647L;
	if (lv < (-2147483647L - 1)) lv = -2147483647L - 1;
	return (int)lv;
}
static int   SafeAtoi(const char* s) { return SafeAtoiLog(s, NULL); }
static float SafeAtof(const char* s) { return (s == NULL) ? 0.0f : (float)atof(s); }

// ==================== 图片加载重试限流（2026-10-16 新增）====================
// ★★ 这条是"选卡/进游戏时随机崩"的头号嫌疑，务必保留 ★★
// 框架的贴图 API 每次调用都会**漏掉一块 ≥1KB 的堆内存**（调用方不回收）：
//   Draw::ToString(names)    → AllocMemory(0, 0x1C) = new BYTE[1024+28]  ⇒ 每次漏 1052 B
//   Draw::GetSharedImage(...) → AllocMemory(0, 4)    = new BYTE[1024+4]   ⇒ 每次漏 1028 B
//   （AllocMemory 的最小块就是 1 页 = 1024 B，所以哪怕只要 4 字节也吃 1KB）
// 而本文件里几乎所有"懒加载贴图"的写法都是：
//       if (!g_xxxLoaded) { g_xxxLoaded = true; LoadXxx(); }
//   loader 内部 __except 失败时把 g_xxxLoaded 复位 ⇒ **下一帧再试一次** ⇒
//   一旦某个 png 缺失/资源未就绪 → **每帧重试 + 每帧漏 ~3KB/图**，4 张图 ≈ 700KB/s，
//   32 位进程 2GB 用户空间几十分钟就被吃干。之后的表现与日志完全吻合：
//     · code=0xE06D7363（std::bad_alloc：operator new 失败被抛）——日志里 34 条，
//       实测同一会话 step=exppouch:images 连续 12 条（经验包 loader 每帧重试）；
//     · code=0xC0000005 且 **fault=0**、EIP 落在 ntdll 堆函数里（堆提交失败后的错误处理路径踩 NULL）。
// ⇒ 统一限流：每个 loader 最多尝试 IMAGE_LOAD_MAX_TRIES 次，之后永久放弃（不再漏）。
//   正常情况（资源就绪）第 1 次就成功，限流不产生任何行为变化。
#define IMAGE_LOAD_MAX_TRIES 600
#define IMGLOAD_SLOTS        24
static int g_imgLoadTries[IMGLOAD_SLOTS] = { 0 };
static bool ImageLoadRetryAllowed(int slot)
{
	if (slot < 0 || slot >= IMGLOAD_SLOTS) return false;
	if (g_imgLoadTries[slot] >= IMAGE_LOAD_MAX_TRIES) return false;
	if (++g_imgLoadTries[slot] >= IMAGE_LOAD_MAX_TRIES)
		CrashStr("[IMGLOAD] a texture loader gave up after 600 tries (png missing?)\r\n");
	return true;
}

// ==================== 经验系统 ====================

// 全局映射表：植物地址 => 经验值
std::map<int, int> g_plantExperience;

// ==================== 等阶系统 ====================
// 等阶阈值: {MaxExp, T1, T2, T3, T4, T5}
// Tier 0: [0, T1)  Tier 1: [T1, T2)  Tier 2: [T2, T3)
// Tier 3: [T3, T4)  Tier 4: [T4, T5)  Tier 5: [T5, MaxExp] (满阶)
std::map<int, std::array<int, 6>> g_seedTierThresholds;

// 默认等阶阈值（豌豆射手配置）
const std::array<int, 6> DEFAULT_TIER = {3000, 250, 800, 1500, 2200, 3000};

// 等阶颜色 (R,G,B): T0白 T1浅绿 T2青 T3黄 T4橙 T5金
static const BYTE TIER_COLOR_R[6] = {0xFF, 0x80, 0x40, 0xFF, 0xFF, 0xFF};
static const BYTE TIER_COLOR_G[6] = {0xFF, 0xFF, 0xE0, 0xDF, 0xA0, 0xDF};
static const BYTE TIER_COLOR_B[6] = {0xFF, 0x80, 0xFF, 0x00, 0x00, 0x00};

// ==================== 攻速系统 ====================
// 攻速配置: 种子类型 => {Speed_T0, Speed_T1, ..., Speed_T5} 单位：秒
std::map<int, std::array<float, 6>> g_seedAttackSpeeds;
const std::array<float, 6> DEFAULT_ATTACK_SPEED = {1.5f, 1.3f, 1.2f, 1.2f, 1.0f, 1.0f};

// ==================== 特殊机制 ====================
// ★ 豌豆射手 5 阶骑士皮肤总开关：1=启用（默认），0=整段禁用（排障用）
//   可用 ini 键 PEASHOOTER_T5_SKIN=0 关闭（免重编即可二分定位）
int g_pst5SkinEnabled = 1;

// ★ 向日葵 3 阶「皇冠+权杖」皮肤总开关：1=启用（默认），0=整段禁用
//   可用 ini 键 SUNFLOWER_3_SKIN=0 关闭（免重编即可二分定位）
int g_sunf3SkinEnabled = 1;

// 击退子弹概率、距离
int g_knockbackProbability = 20;
int g_knockbackDistance = 40;
// 连射概率
int g_doubleShotProbability = 30;
// 击退子弹标记集合（子弹地址）
std::set<int> g_knockbackProjectiles;
// 击退命中 Pow 特效（原版特效表 0x0F"锤子：锤僵尸"，particles\Pow.xml）：
// 命中事件帧只登记坐标，轮询帧播放（粒子生成是重活，事件帧内直接 spawn 会崩——铁律）
static float g_kbPowFxQ[8][2];   // [i][0]=X、[i][1]=Y
static int   g_kbPowFxQCount = 0;
const float KB_POW_FX_DX = 0.0f;    // 特效 X 偏移（相对命中时僵尸 X，位置不对调这里）
const float KB_POW_FX_DY = -60.0f;  // 特效 Y 偏移（相对僵尸基线 Y，负=向上抬）
const int   KB_POW_FX_ID = 0x0F;    // 原版特效表 0x0F"锤子：锤僵尸"（particles\Pow.xml）
// 连射：待发射第二发的植物地址和冷却值
// 用冷却值=1触发第二发，避免递归调用 Shoot() 导致游戏崩溃
static DWORD g_pendingDoubleShotPlant = 0;
static int g_pendingDoubleShotCD = 0;

// ==================== 大喷菇（Fumeshroom, SeedType=10）等阶机制配置 ====================
// 机制实现段在文件后部「大喷菇等阶机制」，全部键以 FUME_ 开头（plant_mechanics.ini）。
//   0阶：同原版
//   1/2/4阶：纯攻速（plant_attack_speed.ini 的 10= 行）
//   3阶：攻击范围（索敌+伤害矩形）向前延伸 FUME_T3_RANGE_EXTEND 像素；粒子同步加长（资源补丁）
//   5阶：每次攻击命中击退 FUME_KB_DISTANCE 像素（巨人砸击状态免疫）
int g_fumeEnabled     = 1;     // 总开关（0=整段停用，大喷菇回到原版行为）
int g_fumeRangeExtend = 160;   // 3阶攻击矩形宽度增量（px，160=2格）
int g_fumeT3PuffDx    = 160;   // 3阶额外补播的那段雾气的 X 偏移（px，0=不补）
int g_fumeKbDistance  = 10;    // 5阶每次攻击的击退距离（px）
int g_fumeKbFrames    = 15;    // 5阶击退平滑分摊帧数（15 帧 ≈ 0.25 秒）
int g_fumeDebug       = 0;     // 自检日志开关（写 D:\pvz_fume_debug.txt）

// 子弹与射击植物的映射表
std::map<int, int> g_projectileShooterMap;

// 字符串缓冲区（用于游戏原生 DrawText 调用）
static int g_stringBuffer = 0;

// 植物死亡经验延迟分配：仅两个 int，无数组无计数，绝对最小化
static int g_lastDeathRow = -1;
static int g_lastDeathExp = 0;

// ==================== 无等阶植物（花盆/睡莲/南瓜头/咖啡豆）===============
// 这四种植物没有等阶、不分配经验、不绘制 Lv/经验字样
// FlowerPot(33) LilyPad(16) Pumpkin(30)
static bool IsNoTierPlant(int seedType)
{
	return seedType == (int)SeedType::FlowerPot
		|| seedType == (int)SeedType::LilyPad
		|| seedType == (int)SeedType::Pumpkin
		|| seedType == (int)SeedType::CoffeeBean;
}

// ==================== 咖啡豆唤醒解锁等阶系统（可复用）====================
// 某些植物（当前：保护伞）默认视为"无等阶"：不分配经验、不绘制 Lv/经验文字；
// 用咖啡豆种在它身上后才解锁等阶系统（之后其他植物要复用时，
// 只需在 IsCoffeeLockPlant 加一行类型判断，其余逻辑全自动生效）。
// 解锁检测在 UpdateUmbrellaFrame 每帧轮询：同格出现咖啡豆植物即标记。
static std::set<DWORD> g_coffeeAwakenedPlants;   // 已被咖啡豆唤醒的植物地址

// 该类型植物是否需要咖啡豆唤醒才解锁等阶/经验
static bool IsCoffeeLockPlant(int seedType)
{
	return seedType == (int)SeedType::UmbrellaLeaf
		|| seedType == (int)SeedType::Marigold;   // 金盏花：与保护伞同规则
}

// 该株植物的等阶/经验是否已解锁（非锁定的植物恒为 true）
static bool IsPlantExpUnlocked(DWORD plantAddress, int seedType)
{
	if (!IsCoffeeLockPlant(seedType))
		return true;
	return g_coffeeAwakenedPlants.count(plantAddress) > 0;
}

// ==================== 经验包（肥料按钮）====================
// 关卡内屏幕右上角、主菜单按钮下方新增一个"经验包"按钮：
//   - 背景框用 ShovelBank.png（同铲子），图标用 Fertilizer.png
//   - 点击按钮选中（再点取消），选中后点击植物：花费阳光给植物加经验
//   - 使用后进入冷却（默认 7.5s）
//   - 阳光花费/经验值/冷却时长由 plant_mechanics.ini 配置
static bool g_expPouchHookInstalled = false;     // Board::MouseDown hook 安装标志
static bool g_expPouchDrawHookInstalled = false; // DrawUITop 入口 hook 安装标志
static bool g_expPouchMouseMoveHookInstalled = false; // Board::MouseMove hook 安装标志（鼠标坐标）
static bool g_expPouchHighlightHookInstalled = false; // Board::DrawGameObjects hook 安装标志（植物高亮）
static DWORD g_expPouchBankImage = 0;            // ShovelBank.png（背景框）
static DWORD g_expPouchIconImage = 0;            // Fertilizer.png（图标）
static DWORD g_expPouchOverlayImage = 0;         // 冷却半透明遮罩
static bool g_expPouchImagesLoaded = false;
static bool g_expPouchSelected = false;          // 是否处于选中（手持）状态
static int g_expPouchCooldownEnd = 0;            // 冷却结束时刻（Board.PlayingTime 厘秒）
static int g_expPouchSunCost = 300;              // 阳光花费
static int g_expPouchExpGain = 300;              // 单次经验值
static int g_expPouchCooldownCs = 750;           // 冷却时长（厘秒，750=7.5秒）
static DWORD g_drawUITopGraphics = 0;            // DrawUITop 入口 hook 保存的 Graphics*
static DWORD g_expPouchGStore = 0;               // ★ Graphics* 存放用堆内存地址（new 分配，绝对可写）
                                                 //   trampoline 的 A3 写这里，避免写 DLL 静态变量地址
                                                 //   （实测 &g_drawUITopGraphics 落在游戏 .text 只读段 → A3 崩溃）
static int g_expPouchBtnX = 0, g_expPouchBtnY = 0; // 经验包按钮位置（绘制时刷新）
static int g_expPouchMouseX = -1, g_expPouchMouseY = -1; // 鼠标实时位置（Board::MouseMove hook 写入堆，绘制时读；-1=未知）
static DWORD g_expPouchMouseStore = 0;           // ★ 鼠标坐标存放用堆内存（new DWORD[2]，trampoline A3 写入，同 g store 方案）

// ==================== 花盆种植放宽 Hook ====================
// 花盆上可以种植任何植物（地刺、水生植物等）。
// 方案：Hook Board::CanPlantAt(0x40E020)。当目标格子上已有花盆、且格子上除
// 花盆/睡莲/南瓜头外没有其他占位植物时，强制返回 0(可以种植)，无视原版的
// "水生只能种水中(3)/需要睡莲(B)/地刺只能种坚硬地面(C)" 等限制。
//
// 调用约定（经反汇编确认）：eax = theGridY(row)，[esp+4] = Board* this，
// [esp+8] = theGridX(col)，[esp+0xC] = theSeedType，被调用者清栈 ret 0xC。
// 返回值：PlantingReason（0=可以种植）。
static bool g_flowerPotHookInstalled = false;

// 紫卡(升级植物) → 底座植物 映射表
// 反汇编 Plant::IsUpgradableTo(0x463470) 逐条确认：
//   0x28→7  0x29→1  0x2A→0xA  0x2B→0x10  0x2C→0x27  0x2D→0x1F  0x2E→0x15  0x2F→0x22
//   机枪豌豆←双发 双子向日葵←向日葵 忧郁菇←大喷菇 香蒲←睡莲 冰西瓜←西瓜投手
//   吸金磁←磁力菇 地刺王←地刺 玉米加农炮←玉米投手(双格，特殊处理)
static int GetUpgradeBase(int seedType)
{
	switch (seedType)
	{
	case (int)SeedType::GatlingPea:   return (int)SeedType::Repeater;     // 40 ← 7
	case (int)SeedType::TwinSunflower: return (int)SeedType::Sunflower;    // 41 ← 1
	case (int)SeedType::Gloomshroom:  return (int)SeedType::Fumeshroom;   // 42 ← 10
	case (int)SeedType::Cattail:      return (int)SeedType::LilyPad;      // 43 ← 16
	case (int)SeedType::WinterMelon:  return (int)SeedType::Melonpult;    // 44 ← 39
	case (int)SeedType::GoldMagnet:   return (int)SeedType::Magnetshroom; // 45 ← 31
	case (int)SeedType::Spikerock:    return (int)SeedType::Spickweed;    // 46 ← 21
	default: return -1; // 非紫卡无需底座（47 玉米加农炮双格特殊，在调用处排除）
	}
}

// 返回 1 = 强制放行（格子上有花盆且无其他占位植物）；返回 0 = 不干预，走原版判定
// 紫卡(升级植物)判定优先级高于花盆放行：必须已有对应底座植物才能种
static int __stdcall CheckCanPlantAtOverride(int row, DWORD boardAddr, int col, int seedType)
{
	int result = 0;

	// 咖啡豆可以种在"需要唤醒解锁等阶"的植物上（当前：保护伞）。
	// 原版咖啡豆只允许种在沉睡的蘑菇上 → 此处对未唤醒的保护伞强制放行；
	// 已唤醒的保护伞不放行（走原版判定被拒绝，防止浪费咖啡豆）。
	if (seedType == (int)SeedType::CoffeeBean
		&& row >= 0 && row <= 5 && col >= 0 && col <= 8 && boardAddr != 0)
	{
		int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
		int plantCount = MemSafeRead<int>(boardAddr + 0xB0);
		if (plantArray != 0 && plantCount > 0)
		{
			for (int i = 0; i < plantCount; i++)
			{
				int p = plantArray + i * 0x14C;
				if (MemSafeRead<BYTE>(p + 0x141)) continue;  // NotExist
				if (MemSafeRead<int>(p + 0x1C) != row) continue;
				if (MemSafeRead<int>(p + 0x28) != col) continue;
				int ptype = MemSafeRead<int>(p + 0x24);
			if ((ptype == (int)SeedType::UmbrellaLeaf || ptype == (int)SeedType::Marigold)
				&& g_coffeeAwakenedPlants.count(p) == 0)
			{
				return 1;   // 放行：咖啡豆种在未唤醒的保护伞/金盏花上
			}
			}
		}
	}

	// 花盆不能叠在花盆上；玉米加农炮需要玉米投手底物+双格检查，不在花盆放行
	if (!(seedType == (int)SeedType::FlowerPot || seedType == (int)SeedType::CobCannon)
		&& row >= 0 && row <= 5 && col >= 0 && col <= 8 && boardAddr != 0)
	{
		// DataArray 是结构体数组(stride=0x14C)，不是指针数组，必须用乘法定位
		int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
		int plantCount = MemSafeRead<int>(boardAddr + 0xB0);
		if (plantArray != 0 && plantCount > 0)
		{
			// 紫卡需要底座：优先级高于花盆放行（如香蒲必须先有睡莲，机枪必须先有双发）
			int requiredBase = GetUpgradeBase(seedType);

			bool hasPot = false;
			bool hasBase = (requiredBase < 0); // 非紫卡无需底座
			for (int i = 0; i < plantCount; i++)
			{
				int p = plantArray + i * 0x14C;
				if (MemSafeRead<BYTE>(p + 0x141)) continue;  // NotExist
				int prow = MemSafeRead<int>(p + 0x1C);
				int pcol = MemSafeRead<int>(p + 0x28);
				if (prow != row || pcol != col) continue;

				int ptype = MemSafeRead<int>(p + 0x24);
				if (ptype == (int)SeedType::FlowerPot) { hasPot = true; continue; }
				// 紫卡底座命中（睡莲是香蒲底座，同时不算占位，可继续放行）
				if (requiredBase >= 0 && ptype == requiredBase) { hasBase = true; }
				// 睡莲/南瓜头不算占位植物：花盆上可继续种水生植物、或给植物套南瓜头
				if (ptype == (int)SeedType::LilyPad || ptype == (int)SeedType::Pumpkin) continue;
				// 格子上已有其他占位植物 → 不干预，走原版判定（原版会处理升级/拒绝）
				goto done;
			}

			// 无占位植物：只有花盆时放行；但紫卡必须已有底座，否则不干预（原版返回"紫卡需要底物"）
			if (hasPot && (requiredBase < 0 || hasBase))
				result = 1;
		}
	}

done:
	return result;
}

// 安装 CanPlantAt hook @ 0x40E020
// 延迟到 onGameObjectsUpdate 首次执行（游戏代码就绪后），与冰锥 hook 同理。
// ★ PUSHAD 压栈顺序: EAX,ECX,EDX,EBX,ESP,EBP,ESI,EDI —— EDI 在栈顶 [esp+0x00]，EAX 在 [esp+0x1C]！
//   PUSHAD 后原参数偏移: this@+0x24 col@+0x28 seedType@+0x2C row(原EAX)@+0x1C
// trampoline 布局（原入口5字节 83 EC 18 53 55 无相对跳转，无需偏移修正）:
//   [0x00] PUSHAD
//   [0x01] push [esp+0x2C]  seedType
//   [0x05] push [esp+0x2C]  col      (push 后 esp-4，偏移保持 0x2C 仍取到 col)
//   [0x09] push [esp+0x2C]  this(Board*)
//   [0x0D] push [esp+0x28]  row      (第4次 push 时 esp=E-0xC，[esp+0x28]=[E+0x1C]=EAX)
//   [0x11] call CheckCanPlantAtOverride   (__stdcall 被调用者清栈)
//   [0x16] test eax, eax
//   [0x18] jnz +0x0B  → 放行分支 [0x25]
//   [0x1A] POPAD
//   [0x1B] <原5字节>
//   [0x20] jmp 0x40E025
//   [0x25] POPAD; xor eax,eax; ret 0xC   ← 放行：返回0(可以种植)
void InstallFlowerPotHook()
{
	DWORD hookAddr = 0x40E020;
	int rawLen = 5;
	BYTE rawCode[5];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, rawCode, rawLen);
	// ★修改器共存：站点已被 PVZTools 等改写时不安装（把它的 E9 rel32 拷进 trampoline
	//   会因 rel32 失配跳飞 → 实测 EIP=trampoline 页尾崩溃）。跳过=花盆放行功能降级。
	{
		static const BYTE kExpected[5] = { 0x83, 0xEC, 0x18, 0x53, 0x55 };
		if (memcmp(rawCode, kExpected, 5) != 0)
		{
			CrashStr("HOOKSKIP name=CanPlantAt site=0x40E020 (bytes changed - modifier?)\r\n");
			return;
		}
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return;

	BYTE tp[64];
	int p = 0;
	tp[p++] = 0x60;                                      // PUSHAD
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x2C; // push [esp+0x2C] seedType
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x2C; // push [esp+0x2C] col
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x2C; // push [esp+0x2C] this
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x28; // push [esp+0x28] row(EAX副本)
	int callOff = (int)&CheckCanPlantAtOverride - (tramp + p + 5);
	tp[p++] = 0xE8; memcpy(tp + p, &callOff, 4); p += 4; // call CheckCanPlantAtOverride
	tp[p++] = 0x85; tp[p++] = 0xC0;                      // test eax, eax
	tp[p++] = 0x75; tp[p++] = 0x0B;                      // jnz +0x0B → [0x25] 放行分支
	tp[p++] = 0x61;                                      // POPAD（正常路径）
	memcpy(tp + p, rawCode, rawLen); p += rawLen;        // 原代码
	int jmpOff = (int)(hookAddr + rawLen) - (tramp + p + 5);
	tp[p++] = 0xE9; memcpy(tp + p, &jmpOff, 4); p += 4;  // jmp back
	tp[p++] = 0x61;                                      // [0x25] 放行分支: POPAD
	tp[p++] = 0x33; tp[p++] = 0xC0;                      // xor eax, eax → 返回0(可以种植)
	tp[p++] = 0xC2; tp[p++] = 0x0C; tp[p++] = 0x00;      // ret 0xC

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);

	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
}

// ==================== 花盆装水贴图（水生植物种在花盆上 → Pot_top → Pot_top2）====================
// 花盆 reanim 的 Pot_top 轨道（轨道名=图片名，金盏花 Marigold_petals 已验证此规律）在格子上有
// 水生植物（睡莲/缠绕海草/海蘑菇/香蒲）时替换为 Pot_top2.png（表示花盆盛水），无水生植物时恢复原图。
// 参考实现：金盏花 SetImageOverride("Marigold_petals", ...) + 撑杆司令每帧幂等覆盖。
// ★ SetImageOverride(0x473490: ecx=reanim, eax=轨道名, [esp]=image, ret 4)；轨道实例 +0x44 = image override。
static DWORD g_potTop2Image = 0;        // Pot_top2.png（游戏内 Image*，延迟加载）
static DWORD g_potTopOrigImage = 0;     // Pot_top.png 原图（恢复用）
static bool g_potTopImageLoaded = false; // 加载标志（onGameObjectsUpdate 首次执行加载）
static std::map<int, bool> g_potTopLastState; // 花盆地址 -> 上次装水状态（状态没变不重复 SetImageOverride）

// 加载花盆替换贴图（__try 独立函数避 C2712，与 LoadMarigoldImages 同模式）
static void LoadPotTopImages()
{
	__try
	{
		DWORD isNew = 0;
		Draw::PString variant = Draw::ToString("");
		Draw::PString fn2 = Draw::ToString("reanim\\Pot_top2.png");
		DWORD r2 = Draw::GetSharedImage(isNew, variant, fn2);
		if (r2) g_potTop2Image = Draw::SharedImageRefToImage(r2);
		Draw::PString fn0 = Draw::ToString("reanim\\Pot_top.png");
		DWORD r0 = Draw::GetSharedImage(isNew, variant, fn0);
		if (r0) g_potTopOrigImage = Draw::SharedImageRefToImage(r0);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_potTopImageLoaded = false;
	}
}

// 是否为水生植物（种在花盆上即"装水"）
static bool IsAquaticPlantType(int seedType)
{
	return seedType == (int)SeedType::LilyPad
		|| seedType == (int)SeedType::TangleKelp
		|| seedType == (int)SeedType::Seashroom
		|| seedType == (int)SeedType::Cattail;
}

// 设置单个花盆的 Pot_top 贴图（hasWater=true → Pot_top2，false → 原图；状态没变则跳过）
static void ApplyPotTopTexture(DWORD plantAddr, bool hasWater)
{
	if (!plantAddr)
		return;
	auto stIt = g_potTopLastState.find(plantAddr);
	if (stIt != g_potTopLastState.end() && stIt->second == hasWater)
		return; // 状态没变，跳过（省每帧执行游戏函数的开销）
	__try
	{
		PVZ::Plant p(plantAddr);
		PVZ::Animation anim = p.GetAnimationPart1();
		DWORD ra = (DWORD)anim.GetBaseAddress();
		// ★★ 2026-10-16：动画未就绪时 GetAnimationPart1() 返回 INVALID_BASEADDRESS = 0x400000
		//   （exe 镜像基址，合法可读，`!base` 拦不住）；必须先卡成"可写堆对象"再谈写轨道。
		if (ra < 0x10000 || ra == 0x400000 || ra >= 0x80000000) return;
		if (!CrashIsWritable(ra, 0xA0)) return;
		// ★ 用纯内存的 ReanimTrackIndex（未命中返回 -1）预检；注意框架 FindTrackIndex
		//   **找不到时返回 0**，所以它的 `< 0` 判断永远不会触发。
		//   ReanimSetImageOverride 内部还会再自检一次（reanim 可写 + 名字真命中 + 目标可写）。
		if (ReanimTrackIndex(ra, "Pot_top") < 0) return;
		DWORD img = hasWater ? g_potTop2Image : g_potTopOrigImage;
		if (!img)
			return;
		ReanimSetImageOverride(ra, "Pot_top", img);
		g_potTopLastState[plantAddr] = hasWater;
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ==================== 向日葵特殊机制 ====================
// 光环：相邻植物攻速提升百分比（默认30%）
float g_sunflowerAuraBoost = 0.30f;

// ==================== 寒冰射手特殊机制 ====================
// 三/四阶冻结概率（%）
int g_snowPeaFreezeProbability = 10;
// 五阶冰锥概率（%）
int g_snowPeaIcicleProbability = 10;
// 冻结子弹标记集合
std::set<int> g_snowPeaFreezeProjectiles;
// 冰锥子弹标记集合
std::set<int> g_snowPeaIcicleProjectiles;
// 冰锥已命中僵尸集合（穿透用：冰锥地址 -> 已命中僵尸地址集合）
std::map<int, std::set<int>> g_icicleHitZombies;

// ===== 杨桃（Starfruit, SeedType=29）弹射机制 =====
// 子弹方向（屏幕坐标：x 右正、y 下正）
enum StarDir {
	SD_NONE = 0, SD_UP, SD_DOWN, SD_BACK, SD_FWD,
	SD_UR60, SD_DR60, SD_UR45, SD_DR45, SD_UL45, SD_DL45
};
// 各方向单位向量（用于设定/改写子弹速度）
// ★ UR60/DR60 = 原版对角星实际角度：距水平面 30° 仰角（= 距垂直线 60°），
//   反汇编铁证：0x45F7xx 用 cos(30°)/sin(30°)（0x639f90=cos, 0x63a180=sin）×3.33 速度
static const float STAR_DIR_VEC[11][2] = {
	{0,0},                                  // NONE
	{0,-1},                                 // UP
	{0, 1},                                 // DOWN
	{-1,0},                                 // BACK
	{1, 0},                                 // FWD
	{0.8660254f,-0.5f},                     // UR60（30° 仰角）
	{0.8660254f, 0.5f},                     // DR60（30° 俯角）
	{0.7071068f,-0.7071068f},               // UR45
	{0.7071068f, 0.7071068f},               // DR45
	{-0.7071068f,-0.7071068f},              // UL45
	{-0.7071068f, 0.7071068f},              // DL45
};
// 命中后弹射到的下一方向（SD_NONE = 无后续弹射）
//   3阶: 1次弹射；4/5阶: 45°子弹可弹2次（左右交替翻转），60°方向仅弹1次
static const StarDir STAR_NEXT_DIR[11] = {
	SD_NONE,  // NONE
	SD_DR45,  // UP   -> 右下45
	SD_UR45,  // DOWN -> 右上45
	SD_FWD,   // BACK -> 正前
	SD_NONE,  // FWD  -> (未定义，直飞)
	SD_DR60,  // UR60 -> 右下60
	SD_UR60,  // DR60 -> 右上60
	SD_DR45,  // UR45 -> 右下45 (45°通用翻转)
	SD_UR45,  // DR45 -> 右上45 (45°通用翻转)
	SD_UR45,  // UL45 -> 右上45
	SD_DR45,  // DL45 -> 右下45
};
// 单发子弹状态
struct StarfruitState {
	StarDir dir;             // 当前方向（SD_NONE=未归类，齐射尾 hook 归类）
	int bounceIndex;         // 已弹射次数
	int maxBounces;          // 可弹射上限（3阶=1 / 4,5阶=2）
	std::set<int> hitZombies;// 已命中僵尸地址（防二次判定）
};
std::map<int, StarfruitState> g_starfruitState;     // 子弹地址 -> 状态
std::map<int, int> g_starfruitAttackCount;         // 植物地址 -> 攻击次数（5阶暴击计数）
// ★ 齐射循环动态上限：齐射尾 hook 的 trampoline 用 cmp eax,[本变量] 替换原 cmp eax,5。
//   5阶暴击时置 8 → 原生 5 星循环扩展为 8 星（星 5-7 无原生方向，由尾 hook 定向），
//   末星处理完复位 5。hook 未安装时保持 5（原版行为）。
int g_starVolleyLimit = 5;
float g_starfruitSpeed = 3.33f;                    // 杨桃子弹速度缓存（原版实测 3.33）
const int STARFRUIT_DAMAGE = 20;                   // 杨桃子弹伤害（与原版一致）
// 齐射尾 hook 已安装标志（延迟到 onGameObjectsUpdate 首次执行时安装，防启动早期代码未解密）
static bool g_starVolleyHookInstalled = false;
// 冰锥自定义贴图（游戏内 Image 对象地址）
static DWORD g_icicleImageAddr = 0;
// 雪晶（3/4阶冻结子弹）自定义贴图
static DWORD g_snowCrystalImageAddr = 0;
// 西瓜大炮弹（5阶西瓜投手最后一发）放大版弹体贴图（Melonpult_melon 1.5x，ProjectileMelonBig.png）
static DWORD g_melonBigImageAddr = 0;
// 小冰瓜（5阶冰西瓜大招散射弹）80% 缩小贴图（WinterMelon_projectile 0.8x，ProjectileIceMelonSmall.png）
static DWORD g_iceMelonSmallImageAddr = 0;
// 击退子弹（豌豆射手3阶+）自定义贴图（ProjectileKnockbackPea.png，标记97）
static DWORD g_knockbackPeaImageAddr = 0;
// 贴图已加载标志（延迟到 onGameObjectsUpdate 首次执行时加载）
static bool g_icicleImageLoaded = false;
// 冰锥贴图 hook 已安装标志（延迟到游戏代码就绪后安装，防止启动早期读到垃圾原代码）
static bool g_icicleHookInstalled = false;
// 已加速的冰锥子弹地址集合（一次性 1.5 倍速，防止重复叠加）
std::set<int> g_speedBoostedIcicles;
// 冰锥上一帧 X 坐标（测量游戏实际移动距离，额外补 50% 实现 1.5 倍速）
std::map<int, float> g_iciclePrevX;

// ==================== 双发射手特殊机制 ====================
// 冰豌豆概率 (%)
int g_repeaterIcePeaProbability = 20;
// 火豌豆概率 (%)
int g_repeaterFirePeaProbability = 20;
// 冰火豌豆概率 (%)
int g_repeaterIceFirePeaProbability = 20;
// 冰火豌豆标记集合
std::set<int> g_repeaterIceFireProjectiles;
// 冰火豌豆延迟减速映射: 僵尸地址 → 减速持续时长(厘秒)
std::map<int, int> g_pendingIceFireDecelerates;

// ==================== 卷心菜投手特殊机制 ====================
// 3阶：每次向本行前2个僵尸各投掷1枚卷心菜
// 4阶/5阶：每次向本行前3个僵尸各投掷1枚卷心菜（原5阶机制下调到4阶）
// 5阶弹射：每枚卷心菜命中死亡后，弹射一次——向命中点后方最近的僵尸再投 1 枚
// 实现（最终版，C++ 散射 + 极简 trampoline）：
//  - hook 0x464C1C（投掷函数发射点，原代码 mov edx,[edi+1C]; push edx; push edi）
//    → trampoline 判定植物类型==Cabbagepult(32) → call CabbageScatter(edi) → 跳函数末尾
//  - CabbageScatter(C++)：遍历本行僵尸按 X 排序取前 N 个（3阶=2、4/5阶=3），
//    逐个用游戏原生发射 466E00(植物,僵尸,行,1)；冷却补偿 [edi+58]=原值-180+发射数*60
//  - 弹射（S4 式"子弹从命中点起跳"，非从植物位置重投）：
//    onProjectileRemove 只登记 {plant, 命中X, 影子Y(+0x4C 地面), Row}（POD 队列，
//    Die 事件栈内不干重活），下一帧 tick 结算：临时把植物 ImageX/ImageY 挪到命中点
//    （原生 Fire 466E00 的出生点由 [+8]/[+C] 推导，0x4671E3: 出生x=ImageX+0x19、
//    出生y=ImageY-0x2E）→ 原生 466E00 投向命中点后方最近僵尸 → 立即还原 ImageX/Y。
//    同一 C++ 同步段内 set/restore，无渲染穿插；轨迹/索敌标签/伤害归属全走原生路径
//    → 击杀经验正确归卷心菜投手（非无来源伤害）。
//    弹射弹出生即 [+0x74]=0 宽限 20 帧（防与刚命中的僵尸重叠二次判定），ex>=20 由
//    tick 重新装填原生 +0x74（与原版落地检查 ex>20 宽限对齐）；并标记 g_cabbageNoBounce
//    防连锁（每发子弹只跳一次）
//  - 标记用 DLL 内存数组 g_cabbageMarks[僵尸index]，不污染游戏内存
// 不在游戏索敌函数内部 hook（寄存器依赖极脆弱）；发射必须用 466E00（CreateProjectile 不显示）
static bool g_cabbageExtraShooting = false;  // 散射发射期间防 onPlantAddProjectile 递归/攻速二次缩放
static BYTE g_cabbageMarks[1024] = { 0 };    // 已索敌标记（僵尸 index -> 1），散射用
static bool g_cabbageHookInstalled = false;  // hook 延迟安装标志（代码解密后）

// T5 弹射：命中死亡的弹体登记（POD 定长队列，事件帧只写 POD，禁 map/vector——崩溃铁律）
// vel/xs = 命中瞬间垂直/水平速度（纯物理反弹用：纵向反向、总动量等比缩小）
struct CabbageBounceReq { DWORD plant; float x; float y; int row; float vel; float xs; };
static CabbageBounceReq g_cabbageBounceQ[16];
static int g_cabbageBounceCount = 0;
// 已弹射过的弹体（地址→1）：弹射新弹死亡后不再弹射（防无限连锁）。
// 轮询帧插入 / 事件帧 erase（onProjectileRemove 大量 map erase 先例，安全）
static std::map<DWORD, int> g_cabbageNoBounce;

// T5 弹射弹的"碰撞宽限期"登记表：弹射弹出生点就在刚命中的僵尸脚下（从命中点起跳），
// 第 1 帧碰撞扫描必然与该僵尸重叠 → 会打回同一只而非弹过它。
// 对策（西瓜大炮 +0x74 清标签的逆向运用）：出生即写 [+0x74]=0（0x531A80 标签检查失败→
// 碰撞扫描全跳过），前 20 帧无碰撞飞行；原版落地检查自带 ex>20 宽限（0x46D598），
// ex>=20 时由 tick 重新装填原生 +0x74 —— 两个宽限期严格对齐，无碰撞空洞窗口。
// 槽位带 Id(+0x90) 校验，防弹体死亡后地址被内存池复用误写他人弹体。
struct CabbageBounceArm { DWORD proj; int id; int orig74; };
static CabbageBounceArm g_cabbageBounceArm[16];
static int g_cabbageBounceArmCount = 0;

// ==================== 西瓜投手等阶机制（T3连投 / T4最多5连 / T5西瓜大炮）====================
//  - 3阶: 42% 概率两连投（[+0x58]=1 → 游戏下一帧原生补发，豌豆射手连射同款机制）
//  - 4阶: 连投的每一发继续判定连投，单轮最多 5 连
//  - 5阶: 每轮最后一发变为西瓜大炮（S4 同机制）：
//      ★ 真落地触发（S4"子弹综算"完整复刻）：逐帧把 DamageAbility(+0x74) 清 0（游戏创建
//        子弹时会写该字段，只在发射时清一次会被覆盖 → 必须 tick 每帧重清，S4 也是每帧清）
//        → 弹体不与任何僵尸碰撞、飞过头顶自由下落；下落中 Height(+0x38)<=阈值时原版
//        自带落地死亡（0x46D826→0x46E000→Die），onProjectileRemove 只做"记录待结算"，
//        下一帧 tick 再做特效/音效/伤害（不在 Die 事件栈内干重活）。
//        爆炸/群伤锚定 ShadowY(+0x4C)（弹体正下方地面）。
//      单层樱桃爆炸（0x04）贴图替换为 IMAGE_MELONPULT_PARTICLES（0x6A73BC，西瓜泼溅大图，
//      不缩放——特效不放大）；飞行中的大炮弹贴图放大 150%：标记 [proj+0x78]=95 →
//      绘制 hook 0x46E6C7 替换为 images\ProjectileMelonBig.png（Melonpult_melon 1.5x）；
//      音效 55(CherryExplode) + 命中 62(MelonHit)（S4 同款，LowerSoundType 实测映射），
//      本行落点前后 1.375 格(±110px) 无衰减群伤（伤害导出 ini），邻行前后 0.5 格(±40px) 40 点；
//      ★有来源伤害：命中前写僵尸伤害来源字段（z+0x148）= 发射西瓜地址（金盏花同款），
//      击杀经验归西瓜；Board 必须用 LawnApp+0x768（旧版误传 LawnApp = 零伤害根因）
// 卡3阶未选路线的西瓜等阶压制为 2（MelonClampTier），不触发任何机制；选"冰瓜路线"后
// 植物替换为 WinterMelon(44)，天然不进本分支
static float g_melonChainProbability = 42.0f;   // MELON_CHAIN_PROBABILITY 连投概率(%)
static int   g_melonCannonDamage = 220;         // MELON_CANNON_DAMAGE 大炮本行群伤
const int    MELON_CANNON_SIDE_DAMAGE = 40;     // 邻行群伤（需求明确不导出，代码常量）
static int   g_melFxErr = 0;                    // 大炮特效 __except 留痕（排障铁律）

// ==================== 冰西瓜（WinterMelon, SeedType=44）等阶机制 ====================
// 冰西瓜由西瓜投手右键选路线B 替换而来（见"西瓜投手升级路线选择"），保留等阶/经验。
//  - 0~3阶: 无新机制（原版冰瓜：伤害20 + 命中减速）
//  - 4阶: 冰瓜命中僵尸时 ICE_MELON_FREEZE_PROBABILITY% 概率冻结 4 秒（Froze(400)）
//  - 5阶: 每 5 次普攻触发一次"冰瓜大招"：
//      本行按 X 排序的第 1 只僵尸吃一发普通冰瓜（原版伤害/减速，走原生结算），
//      第 2 ~ (1+ICE_MELON_VOLLEY_COUNT) 只僵尸各散射一枚"小冰瓜"
//      （伤害 10 + 减速，硬编码；贴图 80% = images\ProjectileIceMelonSmall.png）。
//  ★ 有来源伤害：大招弹逐枚写 zombie+0x148 = 冰西瓜地址（击杀经验归冰西瓜）；
//    小冰瓜的自定义伤害走 onProjectileHitZombie 的标记分支（标记在 DLL 数组，不污染游戏内存）。
//  标记复用 [proj+0x8C]（豌豆染色通道；冰瓜弹不可能过火/染色，无冲突）。
static int   g_iceMelonFreezeProbability = 20;  // ICE_MELON_FREEZE_PROBABILITY 4阶冻结概率(%)
static int   g_iceMelonVolleyCount = 14;        // ICE_MELON_VOLLEY_COUNT 5阶散射小冰瓜数量(枚)
const int    ICE_MELON_FREEZE_CS = 400;         // 4阶冻结时长（厘秒，400=4秒；需求明确不导出）
const int    ICE_MELON_SMALL_DAMAGE = 10;       // 小冰瓜伤害（需求明确不导出）
const int    ICE_MELON_VOLLEY_PERIOD = 5;       // 5阶大招触发周期（每 5 次普攻；需求明确不导出）
const int    ICE_MELON_SMALL_MARK = 200;        // 小冰瓜标记值（[proj+0x8C]，豌豆标记只用 1/2/3）
// 5阶普攻计数（植物地址 -> 累计普攻次数，DLL 侧记录，不写游戏对象）
struct IceMelonCount { DWORD plant; int count; };
static IceMelonCount g_iceMelonShots[32];
static bool  g_iceMelonVolleyActive = false;    // 大招发射期间防 onPlantAddProjectile 攻速二次缩放
static int   g_iceMelonFxErr = 0;               // __except 留痕（排障铁律）
// 待开大队列（POD 定长，onPlantAddProjectile 只登记，轮询帧消费）
static DWORD g_iceMelonVolleyQ[8];
static int   g_iceMelonVolleyQCount = 0;

// 大招"分帧发射"任务队列（POD 定长）：每帧只消费一枚，避免同帧连调 0x466E00
struct IceMelonTask { DWORD plant; DWORD zombie; int small; };
static IceMelonTask g_iceMelonTasks[20];
static int          g_iceMelonTaskCount = 0;
static const int    ICE_MELON_TASK_MAX  = 20;

// 待播放命中特效队列（POD 定长）：小冰瓜命中事件帧只登记坐标，
// 下一帧轮询帧（IceMelonFreezeFrame）在安全上下文 spawn 原版"冰瓜：破裂"特效（0x01）。
// ★ 粒子生成绝不能放在命中事件帧内（同寒冰菇/IceFieldFrame、西瓜大炮 MelonPendingSplash 先例）。
// ★ 特效不缩放（需求明确）：直接 spawn 原版 0x01，不做 OverrideScale。
struct IceMelonFxReq { float x, y; };
static const int ICE_MELON_HIT_EFFECT = 0x01;   // 数值表"01 冰瓜：破裂"（原版冰瓜命中特效）
static IceMelonFxReq g_iceMelonFxQ[16];
static int   g_iceMelonFxQCount = 0;

// 冻结后减速窗口（POD 定长）：★声明必须位于 IceMelonResetShots 之前（其重置逻辑引用本数组）
struct IceMelonFreezeGrace { DWORD zombie; int polls; };
static IceMelonFreezeGrace g_iceMelonFreezeGrace[16];
static int g_iceMelonFreezeGraceCount = 0;

// ---- 冰西瓜命中 POD 诊断（命中事件帧禁 fopen/CRT → 只写这些普通变量）----
// 轮询帧（IceMelonFreezeFrame）检测序列号变化后用 IceLog 统一落盘。
// 背景：上一轮把 IceLog(fopen) 放进命中事件帧属违规——fopen 异常被事件外层 __except 吞掉
// → return 0（判未命中）→ 冻结逻辑整体失效 + 0 条日志（2026-09-11 日志实锤）。
static volatile DWORD g_iceDiagHitSeq   = 0;   // 普通冰瓜命中判定次数（事件帧递增）
static volatile DWORD g_iceDiagSmallSeq = 0;   // 小冰瓜命中次数（事件帧递增）
static volatile DWORD g_iceDiagProj     = 0;   // 最近一次普通冰瓜命中：弹体地址
static volatile DWORD g_iceDiagZombie   = 0;   // 最近一次普通冰瓜命中：僵尸地址
static volatile DWORD g_iceDiagMapSrc   = 0;   // 最近一次普通冰瓜命中：来源植物地址
static volatile int   g_iceDiagStier    = 0;   // 最近一次普通冰瓜命中：来源等阶
static volatile int   g_iceDiagRoll     = 0;   // 掷点结果（-1 = 等阶不足未掷）
static volatile int   g_iceDiagFroze    = 0;   // 本次命中是否执行了 Froze
static volatile int   g_iceDiagMark     = 0;   // 命中时 [proj+0x8C] 原始值（诊断用）
static volatile int   g_iceDiagPtype    = 0;   // 命中时 [proj+0x5C] 弹体类型（诊断用）
// 小冰瓜"命中结算"诊断：确认最终结算在哪只僵尸身上
static volatile DWORD g_iceDiagSmallHitProj    = 0;
static volatile DWORD g_iceDiagSmallHitZ       = 0;

// 游戏原生发射函数 0x466E00(植物, 僵尸, 行, 变体)，stdcall ret 0x10（与卷心菜散射同款）
typedef int (__stdcall *FnMelonShoot)(int plant, int zombie, int row, int variant);
static FnMelonShoot fnMelonShoot = (FnMelonShoot)0x466E00;

// 前置声明：粒子生成（定义在文件后段，IceMelonFreezeFrame 需在其定义前引用）
static DWORD SeaBurstSpawnParticle(float x, float y, int effectId);
// 前置声明：冰西瓜排障日志（定义在文件后段 ~2688）
static void IceLog(const char* fmt, ...);

static int IceMelonFindShot(DWORD plant)
{
	for (int i = 0; i < 32; i++)
		if (g_iceMelonShots[i].plant == plant) return i;
	return -1;
}
static void IceMelonResetShots()
{
	for (int i = 0; i < 32; i++) { g_iceMelonShots[i].plant = 0; g_iceMelonShots[i].count = 0; }
	g_iceMelonVolleyQCount = 0;
	g_iceMelonVolleyActive = false;
	for (int i = 0; i < 8; i++) g_iceMelonVolleyQ[i] = 0;
	g_iceMelonTaskCount = 0;
	for (int i = 0; i < ICE_MELON_TASK_MAX; i++)
	{
		g_iceMelonTasks[i].plant = 0;
		g_iceMelonTasks[i].zombie = 0;
		g_iceMelonTasks[i].small = 0;
	}
	g_iceMelonFreezeGraceCount = 0;
	for (int i = 0; i < 16; i++) g_iceMelonFreezeGrace[i].zombie = 0;
	g_iceMelonFxQCount = 0;
	for (int i = 0; i < 16; i++) { g_iceMelonFxQ[i].x = 0.0f; g_iceMelonFxQ[i].y = 0.0f; }
}

// 连投槽位（POD 数组，支持多株西瓜同时连投；连投窗口只有几帧，8 个槽位足够）
struct MelonChain { DWORD plant; int count; int savedCD; };
static MelonChain g_melChains[8];
static MelonChain* MelonChainFind(DWORD plant)
{
	for (int i = 0; i < 8; i++)
		if (g_melChains[i].plant == plant) return &g_melChains[i];
	return 0;
}
static MelonChain* MelonChainAlloc(DWORD plant)
{
	for (int i = 0; i < 8; i++)
		if (g_melChains[i].plant == 0)
		{
			g_melChains[i].plant = plant;
			g_melChains[i].count = 0;
			g_melChains[i].savedCD = 0;
			return &g_melChains[i];
		}
	return 0;
}
static void MelonChainFree(MelonChain* ch) { ch->plant = 0; ch->count = 0; ch->savedCD = 0; }
static void MelonChainResetAll()
{
	for (int i = 0; i < 8; i++) { g_melChains[i].plant = 0; g_melChains[i].count = 0; g_melChains[i].savedCD = 0; }
}
// 大炮弹槽位（POD 定长 + Id 校验，项目铁律）：plant = 发射者地址（击杀经验归属）
struct MelonCannonSlot { DWORD proj; DWORD plant; int id; int active; int stall; float lastVisY; };
static MelonCannonSlot g_melonCannonSlots[8];
// 落地待结算（onProjectileRemove 只记录坐标+来源，下一帧 tick 结算——不在 Die 事件栈内做粒子/音效/伤害）
struct MelonPendingSplash { int active; float x; float groundY; int row; DWORD plant; };
static MelonPendingSplash g_melonPendingSplash = { 0, 0.0f, 0.0f, 0, 0 };
static MelonCannonSlot* MelonCannonFind(DWORD proj)
{
	for (int i = 0; i < 8; i++)
		if (g_melonCannonSlots[i].active && g_melonCannonSlots[i].proj == proj)
			return &g_melonCannonSlots[i];
	return 0;
}
static void MelonCannonResetAll()
{
	for (int i = 0; i < 8; i++)
	{
		g_melonCannonSlots[i].proj = 0;
		g_melonCannonSlots[i].plant = 0;
		g_melonCannonSlots[i].id = 0;
		g_melonCannonSlots[i].active = 0;
		g_melonCannonSlots[i].stall = 0;
		g_melonCannonSlots[i].lastVisY = 0.0f;
	}
	g_melonPendingSplash.active = 0;
	g_melonPendingSplash.plant = 0;
}
// 标记西瓜大炮弹：DamageAbility(+0x74) 先清一次（发射帧保险）；游戏创建子弹时仍可能
// 重写该字段 → 真正的清除由 MelonCannonTick 每帧重做（S4"子弹综算"就是每帧清）。
// 落地由原版抛射落地死亡 / MelonCannonTick 兜底判定。
static void MelonCannonMark(DWORD proj, DWORD plant)
{
	for (int i = 0; i < 8; i++)
	{
		if (g_melonCannonSlots[i].active) continue;
		g_melonCannonSlots[i].proj = proj;
		g_melonCannonSlots[i].plant = plant;
		g_melonCannonSlots[i].id = MemSafeRead<int>(proj + 0x90);
		g_melonCannonSlots[i].active = 1;
		g_melonCannonSlots[i].stall = 0;
		g_melonCannonSlots[i].lastVisY = 0.0f;
		MemSafeWrite<int>(proj + 0x74, 0);   // 索敌标签清 0 → 碰撞扫描全跳过
		// 弹体贴图标记 95（0x78 通道：90/91=冰锥/雪晶已用；西瓜弹不过火炬，
		// 原生 lastTorchCol 不会被覆写）→ 绘制 hook 0x46E6C7 换放大版西瓜弹贴图
		MemSafeWrite<int>(proj + 0x78, 95);
		return;
	}
	// 槽位满（场上大炮弹 >8，理论不可能）→ 放弃标记，该发退化为普通西瓜
}

// ==================== 冰西瓜 5阶大招（散射小冰瓜）====================
// 与卷心菜散射同架构：C++ 侧遍历本行僵尸排序后用游戏原生 0x466E00 逐枚发射。
//   - 第 1 只（X 最小 = 最靠前）: 普通冰瓜（原生结算：伤害 20 + 减速），不打自定义标记
//   - 第 2 ~ (1+count) 只: 各一枚小冰瓜 → 发射后写 [proj+0x8C]=200 标记
//     → onProjectileHitZombie 按标记走"10 伤害 + 减速"自定义分支
// ★★ 时序：本函数含 std::vector/std::sort + std::map 插入，绝不能在 onPlantAddProjectile
//   事件帧内运行（崩溃铁律：hook 帧禁 CRT/非平凡析构）。故 onPlantAddProjectile 只登记
//   "待开大"的植物地址（POD 队列），下一帧 onGameObjectsUpdate 消费 → 在安全上下文发射。
static void IceMelonVolley(DWORD plantAddr)
{
	CRASH_STEP("icemelon:volley");
	int row = MemSafeRead<int>(plantAddr + 0x1C);
	DWORD boardAddr = MemSafeRead<int>(plantAddr + 4);
	if (!boardAddr) return;

	PVZ::Board board(boardAddr);
	auto zombies = board.GetAllZombies();
	// ★★ Bug A 根因（2026-09-10）：原实现收集的是 (Index, X) 再 `PVZ::Zombie z0(rowZ[0].first)`。
	//   Zombie 构造函数按"值 > 65535 当地址，否则当索引"解释参数，而 Zombie::Index = Id & 0xFFFF
	//   恒 < 65536 → 走索引分支 → BaseAddress = [LA+0x90] + Index*0x15C。僵尸池里 Index 与物理槽位
	//   并不等价（死亡槽位会被复用、Index 来自 Id 低 16 位），于是 rowZ[0].first 算出的地址可能
	//   根本不是那只僵尸、甚至落在别的槽位 → 第 1 只的正常冰瓜飞到错误目标/落空，
	//   视觉上就成了"小冰瓜从第 1 只开始散射"。
	//   修法：全程保存并直接使用僵尸**地址**（GetBaseAddress 恒 > 65535），杜绝二次索引换算。
	std::vector<std::pair<DWORD, float>> rowZ;   // (zombie address, X)
	for (auto& z : zombies)
	{
		if (z.NotExist) continue;
		if (z.Hypnotized) continue;
		if ((int)z.Row != row) continue;
		DWORD za = (DWORD)z.GetBaseAddress();
		if (!za) continue;
		rowZ.push_back(std::make_pair(za, z.X));
	}
	if (rowZ.empty()) return;
	std::sort(rowZ.begin(), rowZ.end(),
		[](const std::pair<DWORD, float>& a, const std::pair<DWORD, float>& b) { return a.second < b.second; });

	// ★★ 大招目标分配（2026-09-11 定稿，用户实测纠正）：
	//   触发大招的那一次**普攻本身**已经在打了（本植物的正常攻击，瞄准本行最靠前的僵尸），
	//   所以大招**绝不能再给第 1 只补一发普通冰瓜** —— 否则场上只有 1 只僵尸时，
	//   它就是"普攻一发 + 大招再补一发"，共两发砸在同一只头上（12:40 日志实锤：两个不同
	//   弹体 0x1C02DAE8 / 0x1C02DB7C 都命中同一只 z=0x1BF846F0，且都 mark=0）。
	//   → **大招只出小冰瓜，目标 = 第 2 ~ (1+count) 只**（需求原文：第2只~第15只各一枚，共14枚）。
	//     第 1 只由植物自身的普攻负责，不重复、不多发。
	//   → 场上僵尸 ≤1 只时 planned=0，大招不发射任何弹体（彻底消除"只有1只还扔两发"）。
	int planned = 0;
	for (int i = 1; i < (int)rowZ.size() && planned < g_iceMelonVolleyCount; i++)
	{
		if (g_iceMelonTaskCount >= ICE_MELON_TASK_MAX) break;
		g_iceMelonTasks[g_iceMelonTaskCount].plant  = plantAddr;
		g_iceMelonTasks[g_iceMelonTaskCount].zombie = rowZ[i].first;
		g_iceMelonTasks[g_iceMelonTaskCount].small  = 1;
		g_iceMelonTaskCount++;
		planned++;
	}

	// 冷却：大招整轮按发射数适度补偿，避免立即再次触发（每枚 +6 厘秒）
	if (planned > 0)
	{
		int cd = MemSafeRead<int>(plantAddr + 0x58);
		cd += planned * 6;
		MemSafeWrite<int>(plantAddr + 0x58, cd);
	}
	IceLog("VOLLEY plan: plant=0x%X row=%d totalZ=%d planned=%d z0x=%d",
		plantAddr, row, (int)rowZ.size(), planned, (int)rowZ[0].second);
}

// 每帧轮询（onGameObjectsUpdate 调用）：消费"待开大"队列 → 在安全上下文执行散射。
// __try 外壳 + g_iceMelonFxErr 留痕（排障铁律）。
static void IceMelonVolleyFrame(DWORD boardAddress)
{
	(void)boardAddress;
	// ① 消费"待开大"队列 → 规划成分帧发射任务（此处不发射）
	if (g_iceMelonVolleyQCount > 0)
	{
		__try
		{
			for (int i = 0; i < g_iceMelonVolleyQCount; i++)
			{
				DWORD p = g_iceMelonVolleyQ[i];
				g_iceMelonVolleyQ[i] = 0;
				if (!p) continue;
				// 植物仍存活且仍是冰西瓜（地址可能被内存池复用）
				if (MemSafeRead<BYTE>(p + 0x141)) continue;
				if (MemSafeRead<int>(p + 0x24) != (int)SeedType::WinterMelon) continue;
				IceMelonVolley(p);
			}
		}
		__except (EXCEPTION_EXECUTE_HANDLER)
		{
			g_iceMelonFxErr++;
		}
		g_iceMelonVolleyQCount = 0;
	}

	// ② 每帧只发射一枚：★ 同帧连调 0x466E00 达 15 次属非原生调用模式，改为逐帧发射
	if (g_iceMelonTaskCount > 0)
	{
		__try
		{
			IceMelonTask t = g_iceMelonTasks[0];
			for (int i = 1; i < g_iceMelonTaskCount; i++) g_iceMelonTasks[i - 1] = g_iceMelonTasks[i];
			g_iceMelonTaskCount--;

			if (t.plant && t.zombie
				&& !MemSafeRead<BYTE>(t.plant + 0x141)
				&& MemSafeRead<int>(t.plant + 0x24) == (int)SeedType::WinterMelon
				&& !MemSafeRead<BYTE>(t.zombie + 0xEC))
			{
				int row = MemSafeRead<int>(t.plant + 0x1C);
				g_iceMelonVolleyActive = true;
				int proj = fnMelonShoot((int)t.plant, (int)t.zombie, row, 1);
				g_iceMelonVolleyActive = false;
				if (proj)
				{
					if (t.small)
					{
						MemSafeWrite<int>(proj + 0x8C, ICE_MELON_SMALL_MARK);  // 自定义伤害标记
						MemSafeWrite<int>(proj + 0x78, 96);                    // 80% 小贴图
					}
					// ★ 判定基准：打印每发的真实 XSpeed 与回读的贴图/伤害标记。
					//   mk 是小冰瓜贴图唯一的触发源（绘制 hook 0x46E6C7 判 [proj+0x78]==96），
					//   回读到 mk=96 才说明这发会被画成 80% 小贴图 —— 直接可查，不靠推断。
					float px = MemSafeRead<float>(proj + 0x30);
					float xs = MemSafeRead<float>(proj + 0x3C);
					float hs = MemSafeRead<float>(proj + 0x44);
					int mk = MemSafeRead<int>(proj + 0x78);
					int hm = MemSafeRead<int>(proj + 0x8C);
					IceLog("FIRE small=%d: z=0x%X zx=%d proj=0x%X px=%.0f xs=%.2f hs=%.2f mk=%d hm=%d",
						t.small ? 1 : 0, t.zombie,
						(int)MemSafeRead<float>(t.zombie + 0x2C), proj, px, xs, hs, mk, hm);
				}
			}
		}
		__except (EXCEPTION_EXECUTE_HANDLER)
		{
			g_iceMelonFxErr++;
			g_iceMelonVolleyActive = false;
		}
	}
}

// 冻结后的减速补写（onGameObjectsUpdate 调用，安全上下文）：
//   需求 = "冻结 4 秒，解冻后附 10 秒减速"。
//   ★ 为什么必须逐帧再断言：游戏 Update 在僵尸处于冻结态时会把 +0xAC(DecelerateCountdown)
//     归零（冻结优先于减速）。所以在冻结期内每帧补写 +0xAC=1000，解冻瞬间它自然接续成
//     10 秒减速。窗口以"冻结计时(+0xB4) 是否仍 >0"为存活判据，polls 仅作防泄漏安全阀。
// （IceMelonFreezeGrace 结构与 g_iceMelonFreezeGrace/g_iceMelonFreezeGraceCount 已上移至
//   文件头部全局区 —— IceMelonResetShots 在此之前引用，C++ 要求先声明后使用）
static const int ICE_MELON_THAW_SLOW_CS  = 1000;  // 解冻后减速 10 秒（需求明确，不导出）
static const int ICE_MELON_GRACE_POLLS   = 400;   // 减速再断言窗口上限（帧；仅防泄漏）

// 登记"冻结后减速窗口"（命中事件帧调用，只写 POD）
static void IceMelonAddSlowWindow(DWORD zombieAddr)
{
	if (!zombieAddr) return;
	for (int k = 0; k < g_iceMelonFreezeGraceCount; k++)
		if (g_iceMelonFreezeGrace[k].zombie == zombieAddr)
		{
			g_iceMelonFreezeGrace[k].polls = ICE_MELON_GRACE_POLLS;
			return;
		}
	if (g_iceMelonFreezeGraceCount < 16)
	{
		g_iceMelonFreezeGrace[g_iceMelonFreezeGraceCount].zombie = zombieAddr;
		g_iceMelonFreezeGrace[g_iceMelonFreezeGraceCount].polls = ICE_MELON_GRACE_POLLS;
		g_iceMelonFreezeGraceCount++;
	}
}

static void IceMelonFreezeFrame(DWORD boardAddress)
{
	(void)boardAddress;
	// ---- POD 诊断落盘（轮询帧安全上下文）：命中事件帧只写内存，这里检测序列号变化后 IceLog ----
	static DWORD s_dumpedHitSeq = 0;
	static DWORD s_dumpedSmallSeq = 0;
	bool diagDirty = (g_iceDiagHitSeq != s_dumpedHitSeq) || (g_iceDiagSmallSeq != s_dumpedSmallSeq);
	if (g_iceMelonFreezeGraceCount <= 0 && g_iceMelonFxQCount <= 0 && !diagDirty)
		return;
	__try
	{
		if (g_iceDiagHitSeq != s_dumpedHitSeq)
		{
			IceLog("DIAG hit: seq=%u proj=0x%X z=0x%X mark=%d ptype=%d src=0x%X stier=%d roll=%d froze=%d",
				(DWORD)g_iceDiagHitSeq, (DWORD)g_iceDiagProj, (DWORD)g_iceDiagZombie,
				(int)g_iceDiagMark, (int)g_iceDiagPtype,
				(DWORD)g_iceDiagMapSrc, (int)g_iceDiagStier, (int)g_iceDiagRoll, (int)g_iceDiagFroze);
			s_dumpedHitSeq = g_iceDiagHitSeq;
		}
		if (g_iceDiagSmallSeq != s_dumpedSmallSeq)
		{
			IceLog("DIAG small: seq=%u proj=0x%X z=0x%X",
				(DWORD)g_iceDiagSmallSeq, (DWORD)g_iceDiagSmallHitProj, (DWORD)g_iceDiagSmallHitZ);
			s_dumpedSmallSeq = g_iceDiagSmallSeq;
		}

		// ---- 小冰瓜命中特效（原版"冰瓜：破裂" 0x01，不缩放）----
		for (int i = 0; i < g_iceMelonFxQCount; i++)
		{
			float fx = g_iceMelonFxQ[i].x;
			float fy = g_iceMelonFxQ[i].y;
			g_iceMelonFxQ[i].x = 0.0f;
			g_iceMelonFxQ[i].y = 0.0f;
			if (fx == 0.0f && fy == 0.0f) continue;
			SeaBurstSpawnParticle(fx, fy, ICE_MELON_HIT_EFFECT);
		}
		g_iceMelonFxQCount = 0;

		// ---- 击退命中 Pow 特效（0x0F 锤僵尸，命中一次播一次）----
		for (int i = 0; i < g_kbPowFxQCount; i++)
			SeaBurstSpawnParticle(g_kbPowFxQ[i][0], g_kbPowFxQ[i][1], KB_POW_FX_ID);
		g_kbPowFxQCount = 0;

		// ---- 减速再断言：冻结期内每帧维持 +0xAC，保证解冻后仍有 10 秒减速 ----
		int w = 0;
		for (int k = 0; k < g_iceMelonFreezeGraceCount; k++)
		{
			DWORD zaddr = g_iceMelonFreezeGrace[k].zombie;
			int   left  = g_iceMelonFreezeGrace[k].polls - 1;
			bool keep = false;
			if (left >= 0 && zaddr && CrashIsReadable(zaddr, 0xC0)
				&& !MemSafeRead<BYTE>(zaddr + 0xEC)
				&& MemSafeRead<int>(zaddr + 0x24) != 0)
			{
				int frz = MemSafeRead<int>(zaddr + 0xB4);
				if (frz > 0)
				{
					// 冻结中：维持减速值（游戏 Update 会把 +0xAC 归零）
					MemSafeWrite<int>(zaddr + 0xAC, ICE_MELON_THAW_SLOW_CS);
					keep = true;
				}
				else
				{
					// 已解冻：补一次 10 秒减速后退出窗口
					int cur = MemSafeRead<int>(zaddr + 0xAC);
					if (cur < ICE_MELON_THAW_SLOW_CS)
						MemSafeWrite<int>(zaddr + 0xAC, ICE_MELON_THAW_SLOW_CS);
					keep = false;
				}
			}
			if (keep)
			{
				g_iceMelonFreezeGrace[w].zombie = zaddr;
				g_iceMelonFreezeGrace[w].polls = left;
				w++;
			}
		}
		g_iceMelonFreezeGraceCount = w;
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_iceMelonFxErr++;
		g_iceMelonFreezeGraceCount = 0;
		g_iceMelonFxQCount = 0;
	}
}

// ==================== 裂荚射手特殊机制 ====================
// 0阶：左侧有僵尸→左1发；右侧有僵尸→右1发
// 2阶：左侧有僵尸→左2发；右侧有僵尸→右1发
// 3阶：向左子弹碰屏幕左边反弹；左侧有僵尸→左2发；右侧有僵尸→左2发+右1发
// 5阶：状态A=左2右3 / 状态B=左3右1（升5阶默认A；左键点击切换 + 钱袋星星粒子）
// 实现：hook 0x464B32（裂荚射击分支入口，cmp eax,0x1C; jne）→ SplitPeaShoot(C++) 自定义双向发射
//   - 发射用游戏原生 0x466E00(植物, 0, 行, variant)：variant=1 向左（运动类型[proj+0x58]=6，
//     X-=3.33/帧）、variant=0 向右（运动类型默认0，X+=3.33/帧）——反汇编 0x466E00/0x46D890 证实
//   - 反弹：onGameObjectsUpdate 检测向左子弹（标记92 且运动类型6）X<=40（越界删除点在 X<=-row，
//     安全提前量）→ 改 [proj+0x58]=0 转向右 + 标记改93 + 清该子弹的 lastTorchCol（两次过火关键）
//   - ★★ 字段迁移（2026-08-20）：方向标记/初始X 原存 [proj+0x78]/[0x7C]，
//     但指针表证实 +0x78 是原生"上一次穿过火炬树桩的列数"（OnFire 会覆写）→
//     过火后标记丢失、向左子弹不再反弹！现迁到 [proj+0x80]/[0x84]
//     （炮弹专用字段：0x80=炮下落横坐标初始值 / 0x84=炮目标行，豌豆恒空，安全）
//   - ★★ 两次过火（需求）：火炬在裂荚左边时，向左子弹先过火（原生点火或火炬扫描段兜底首火）
//     → 飞到屏幕左边反弹反向 → 再次穿过同一火炬 → 二次过火升级（弱火→火→炎）。
//     前提是反弹时清 lastTorchCol（否则同列火炬被永久跳过）。
//   - 多颗错开：临时偏移 [植物+0xC]（Y 坐标，int）发射后恢复，避免 N 颗重叠
static bool g_splitPeaHookInstalled = false;  // hook 延迟安装标志（代码解密后）
// ★ onPlantAddProjectile 事件 hook 在 0x4672B5（子弹创建后、运动类型设置前），
//   事件触发时 [proj+0x58] 恒为 0，不能据此判断左右。改用方向队列：
//   SplitPeaShoot 发射前写 g_splitPeaPendingDir（1=向左 / 0=向右），事件同步回调读它标记 [proj+0x80]
static int g_splitPeaPendingDir = -1;          // -1=非裂荚发射
std::map<DWORD, int> g_splitPeaState;         // 植物地址 -> 5阶状态（0=状态A 左2右3 / 1=状态B 左3右1）
const int SPLIT_PEA_LEFT = 92;                // [proj+0x80] 标记：裂荚向左子弹（3阶+，待反弹）
const int SPLIT_PEA_RIGHT = 93;               // [proj+0x80] 标记：裂荚向右子弹 / 已反弹
const int SPLIT_PEA_LEFT_NB = 94;             // [proj+0x80] 标记：低阶向左子弹（不反弹，仅火炬兜底/镜像用）

// ==================== 三线射手特殊机制 ====================
// 需求（2026-08-21）：
//   0-2阶：完全原版（射击动作倒计时==1 时，向上/中/下三路各发射一枚豌豆，某路有目标才发射）
//   3阶：三路各1发；上下路子弹沿正弦弹道飞行并整体漂移交叉（上路的子弹运动到下路、
//        下路的子弹运动到上路，中路直飞）；每次攻击有固定概率开大
//   5阶：三路各2发（共6颗，上下路各2正弦+交叉、中路2直飞）；开大概率上调
//   开大：220 帧内每 3 帧连发 3 颗正弦扇形弹（中间直飞+上下偏正弦），期间不发普通攻击
//   开大概率：plant_mechanics.ini 的 THREEPEATER_ULT_PROB_T3/T5（固定值）
// 参考：S4修猫.txt 三线脚本（464A8F 大招连发 / 45F452 开大判定 / 46DC02 波浪修正），
//   弹道交叉为本项目需求（参考代码"上下路子弹永远留在各自路"被改为交叉漂移）
//
// ★★★ 设计（v5，零 hook，事件登记 + 轮询判定 + 同步注入）：
//   ① onPlantAddProjectile（三线子弹事件）：
//      - 登记普攻弹 {proj, plant}（±θ 大招弹由 TripleUltShoot 内部专用登记）
//      - 一轮3颗按时间窗去重只判首颗：等阶攻速写回+0x58；3阶+按概率开大；
//        5阶未开大 → 豌豆射手双发同款：[+0x58]=1 + g_tripleDblPlant 登记 →
//        游戏下一帧原生触发第二轮完整三路（带射击动画），事件识别恢复冷却（防链式）
//   ② TripleUltShoot（大招齐射，CT 脚本3 同款）：中路直飞 + ±θ 扇形弹；
//      ±θ 弹经 g_triplePendingDir 递归登记后 **同步注入** vx=4.8·cosθ / vy=±4.8·sinθ
//      （fnTripleShoot 已完整返回，写入即最终态——CT 构造后立即写 同款时机）
//   ③ 轮询（onGameObjectsUpdate）：
//      - 处理普攻弹登记：[+0x1C] 行号 vs 植物行 → 上路弹95(目标行+1)/下路弹96(目标行-1)/中路不标
//        （★不能用子弹Y差判上下路：原版三线三颗弹出生Y几乎相同，靠原生YSpeed漂到各行）
//      - 大招状态机：ultTicks 每帧-1，%3==0 齐射；钉住+0x58=400防普攻；结束写回等阶冷却
//      - 95/96: YSpeed = 漂移(±2, 行锁定后 0) + A·cos(ω·t)；行锁定用 PixelToGridY 实测行
//      - 98/99: YSpeed = 基准·(每50帧取反)（CT 脚本1 fchs 同节奏）
//      - 全部每帧重写 YSpeed + 重算行号（CT 同款，交叉后正确索敌）
//   - 0-2阶：仅攻速缩放，纯原版弹道
const int TRIPLE_UP = 95;      // [proj+0x80] 标记：三线上路正弦弹（-A·sin，先向上振动）
const int TRIPLE_DOWN = 96;    // [proj+0x80] 标记：三线下路正弦弹（+A·sin，先向下振动）
const int TRIPLE_ULT_A = 98;   // [proj+0x80] 标记：大招上偏弹（±θ 扇形 + 50帧翻转）
const int TRIPLE_ULT_B = 99;   // [proj+0x80] 标记：大招下偏弹（±θ 取反 + 50帧翻转）
// 正弦弹道参数：Y = 轴Y ± A·sin(ω·t)
//   ★ 轴 = 中路弹道线（植物所在行，即中路子弹的弹道）——上下路子弹没有自己的"路"，
//     都是从中路出发围绕中路上下振动（用户澄清："都是中路的子弹在上下振动"）
//   ★ 95 上路弹：-A·sin（出生 Y=轴Y，先向上振动，之后自然扫过上/中/下路）
//     96 下路弹：+A·sin（反相位，先向下）
//   ★ 振幅 A = 场景行高（振动顶点正好到达上/下路中心线）
static const float TRIPLE_SIN_W = 0.05f;   // 角频率（周期 ≈ 125帧 ≈ 2.1s）
// 大招扇形参数（CT 三线射手代码 同值）
static const float TRIPLE_ULT_SPD = 4.8f;     // 大招弹速度模长
static const float TRIPLE_ULT_THA = 1.14f;    // 扇形角幅度 θmax
static const float TRIPLE_ULT_THW = 0.02856f; // 扇形角扫描角频率（220帧≈2π 整周期扫一个来回）
static int g_threeUltProbT3 = 15;          // 3阶开大概率 %（plant_mechanics.ini 可调）
static int g_threeUltProbT5 = 35;          // 5阶开大概率 %
// 大招状态（POD 定长数组；ultTicks=剩余帧数 219 起每帧-1，%3==0 齐射；0=空闲）
struct TripleState { DWORD plant; int ultTicks; int row; };
static TripleState g_tripleStates[24];
static int g_triplePendingDir = -1;        // 大招发射前设置 98/99（递归事件读取登记；-1=非大招弹）
// 子弹登记（普攻弹轮询帧判行号打标记；±θ 弹 TripleUltShoot 专用同步注入）
struct TriplePendingMark { DWORD proj; DWORD plant; int mark; float theta; };
static TriplePendingMark g_triplePendingMarks[64];
static int g_triplePendingCount = 0;
// 5阶双发（豌豆射手 g_pendingDoubleShot 同款）：[+0x58]=1 → 原生下一帧带动画发第二轮，
// 第二轮首颗事件识别此标记恢复等阶冷却并跳过开大/双发判定（防链式无限双发）
static DWORD g_tripleDblPlant = 0;
static int g_tripleDblCD = 0;
// 攻击去重（一轮3颗+双发第二轮只在首颗做判定）：plant + 板上时间窗
static DWORD g_tripleDedupPlant[8];
static int g_tripleDedupTime[8];
// ★ 子弹标记（DLL 内部 map，不碰原生 [proj+0x80]！）：
//   实测 [proj+0x80] 是原版子弹标志字段（S4修猫脚本1注释：>1=被吸金磁/带归属指针；
//   寒冰写0/1、香蒲当指针用），普通豌豆原生更新代码会读它——写 95/96 这类大值
//   被原生误判 → 子弹固定时间点被移除（t=12/66 + 命中动画 + 无僵尸无墓碑）。
//   裂荚 92/93/94 二进制位不踩原生检查位所以没事，三线 95/96 恰好踩中。
//   故全部标记移入 std::map：轮询帧读写、事件帧 erase（onProjectileRemove 大量先例，安全）。
struct TripleBullet { int mark; float axisY; int plantRow; };
//   mark: 95/96/98/99；axisY=振动轴（出生Y）；plantRow=植物行（边路单侧折叠判定）
static std::map<DWORD, TripleBullet> g_tripleMark;
// ★ 连射队列（③堆叠修复）：当场只发第一颗，其余入队由 onGameObjectsUpdate 每 6 tick 补发一颗
//   （POD 环形队列，SplitPeaShoot 运行在 hook 帧内，严禁 std 容器插入）
struct SplitPeaShot { DWORD plant; int dir; };
static SplitPeaShot g_spShotQueue[128];
static int g_spQueueHead = 0, g_spQueueTail = 0, g_spQueueTimer = 0;
static void SpEnqueue(DWORD plant, int dir)
{
	int next = (g_spQueueTail + 1) % 128;
	if (next == g_spQueueHead) return;   // 满，丢弃（安全）
	if (g_spQueueHead == g_spQueueTail)  // 队列原为空：延迟首发出队，连射间隔均匀（28=双发节奏）
		g_spQueueTimer = 28;
	g_spShotQueue[g_spQueueTail].plant = plant;
	g_spShotQueue[g_spQueueTail].dir = dir;
	g_spQueueTail = next;
}
// ★ 双发去重（①0阶双倍修复）：原版裂荚"向后双发"= 射击分支一周期内被再次触发（0x464B32 二次进入），
//   每次都会全量发射导致数量翻倍。同一植物 newCD/2 时间窗内的第二次调用直接跳过。
static DWORD g_spDedupPlant[32];
static int g_spDedupTime[32];
// ★★★ 防崩溃铁律（2026-08-20 崩溃 0x5E0FFEB0 根因）：
//   onPlantAddProjectile 事件 hook（0x4672B5）运行在游戏执行流中（0x466E00 内部），
//   此处严禁做 std::map 插入/CRT 文件 I/O 等重量级操作（会破坏执行链 → EIP 跳指令中间崩溃）。
//   ★ 方向标记：写 [proj+0x80]=92/93（炮弹专用字段，豌豆恒空）
//   ★ 初始 X（反弹飞行保护）：写 [proj+0x84]（float，同上安全）——事件在子弹构造
//     0x40D620 之后触发，[proj+0x30] 已是原生真实初始 X，零 map 零额外状态。
//   ★ 反弹防重复：反弹后把 [proj+0x80] 改为 93（RIGHT），下一帧不再匹配 92，天然防重复。

// ProjectileImageEvent 实例（在 init() 中延迟创建，避免 DLL 加载时崩溃）
static PVZEvent::ProjectileImageEvent* g_projectileImageEvent = nullptr;

// 向日葵升阶为双子向日葵的暂存数据
static DWORD g_upgradeSunflowerAddr = 0;
static int g_upgradeRow = -1;
static int g_upgradeCol = -1;
static int g_upgradeExp = 0;

// ==================== 路灯花特殊机制 ====================
// 路灯花5阶治疗冷却跟踪: 植物地址 -> 上次治疗时的PlayingTime(厘秒)
std::map<DWORD, int> g_planternHealTimers;

// ==================== 坚果墙（Wallnut）等阶机制 ====================
//   0阶 同原版；1/2/3阶 升级瞬间回满血（贴图受损自动恢复完整）。
//   仅存"升级回血"这一项；不再有死亡留保龄球/亡语机制。
// 每株墙当前等阶（检测升级瞬间回满血）
static std::map<DWORD, int> g_wallnutCurTier;

// ==================== 高坚果（Tallnut, SeedType=23）等阶机制 ====================
//   0阶 血量上限4000；1阶 上限提升并回满血；2阶 抗秒杀（秒杀→扣血，车类被击退）；
//   3阶 每累计受伤2000 → 击退前方1格内最近僵尸1.5格。
// 原版"秒杀植物"三条路径（函数表+反汇编实证）：
//   A) 巨人锤击/压扁头 → Zombie::SquishAllInSquare(0x52E920, type=0) → Plant::Squish(0x462B80)
//   B) 车类碾压（冰车/投石车）→ Zombie::CheckSquish → SquishAllInSquare(type=1)
//   C) 辣椒僵尸爆炸 → Zombie::UpdateZombieJalapenoHead 内 0x527729 直接
//      call Plant::Die(0x4679B0)（逐行遍历植物烧毁，不走 Squish）
// 拦截方案：HookA=0x52E920 入口（type=1 车类整格保护+扣血+击退车1格）、
//   HookB=0x462B80 入口（锤砸/僵王踩踏等：扣血挡下）、HookC=0x527729 调用点（扣血挡烧毁）。
//   扣血后血量<=0 时放行原版（按原版压扁/烧毁死亡）。
// 0阶上限/3阶阈值/击退距离为代码常量（规格仅要求导出 T1 上限与秒杀扣血两个数值）。
static int  g_tallnutT1MaxHp     = 8000;  // TALLNUT_T1_MAXHP  1阶起血量上限
static int  g_tallnutAntiKillDmg = 1000;  // TALLNUT_ANTIKILL_DAMAGE 秒杀转扣血
const int   TALLNUT_T0_MAXHP      = 4000; // 0阶血量上限（代码常量）
const int   TALLNUT_T3_DMG_STEP   = 2000; // 3阶累计受伤触发阈值（代码常量）
const int   TALLNUT_T3_KB_PX      = 120;  // 3阶击退距离 1.5格=120px（代码常量）
const int   TALLNUT_VEHICLE_KB_PX = 80;   // 2阶车类击退 1格=80px（代码常量）
// 每株当前等阶（血量阶梯回满血判定）/上一帧HP/累计受伤（3阶击退）
static std::map<DWORD, int> g_tallnutCurTier;
static std::map<DWORD, int> g_tallnutLastHp;
static std::map<DWORD, int> g_tallnutDmgAcc;
static bool g_tallnutSquishHookInstalled = false; // HookA+B（0x52E920 / 0x462B80）
static bool g_tallnutJalaHookInstalled   = false; // HookC（0x527729 辣椒烧毁调用点）

// ==================== 大蒜（Garlic, SeedType=36）等阶机制 ====================
//   0阶 同原版。血量上限 400（进啃咬态初始化 0x45E23F mov [ebx+0x40],0x190），
//       僵尸啃咬时按"相邻行可用性"随机换行（原版 0x52B902 处 call 0x5AF400 随机 0/1）。
//   1阶 血量上限提升至 GARLIC_T1_MAXHP 并回满血（2/3阶上限不再提升）。
//   2阶 玩家右击大蒜切换"换行方向"（初始向上），方向受关卡行数约束且箭头始终显示实际方向：
//         五行地图（白天/黑夜/屋顶/月夜）: 第1行→只能向下，第5行→只能向上，其余行可自由切换；
//         六行地图（泳池/迷雾）: 第1/3/5行→只能向下，第2/4/6行→只能向上。
//       换行时若指定方向可用则走指定方向，否则回退另一边（两边都不可用=原版不变）。
//   3阶 免疫碾压：巨人无视大蒜（不抬手砸）；即使砸到也不压扁；冰车/投石车碾过不压扁。
//
// ★★★ 行号字段铁律（2026-10-16 反汇编实证，修正旧实现的致命错误）：
//   僵尸**没有** GameObject 的 +0x1C 行号！+0x1C 在僵尸里是动画计时器
//   （构造函数 0x52259C `mov [edi+0x1C],esi`；0x531880 用 `[z+0x6c]` 与 `[z+0x64]` 算 Y）。
//   僵尸行号 = **+0x130**（构造函数 0x522745 `mov [edi+0x130],esi`；esi 即构造参数 route），
//   由巨人扫格遍历器 0x534BB7 `mov ecx,[edi+0x130]` / 0x535017 双重实证。
//   旧实现两处读 `zombie+0x1C` 当行号 ⇒ 2/3 阶全部静默失效（本文件 0x1C 读法一律以本常量替换）。
//   僵尸列号同样没有字段：+0x80 是蹦极目标列（PVZ.h 注释 BungeeColumn）。
//   要列号用僵尸像素 X 整数换算 `(X-25)/80`（GarlicColFromPixelX）。
//   ★ 绝不要为此调用游戏原生 Board::PixelToGridX(0x41C4C0)：它连解 4 层指针且不保存 EBX，
//     在换行 hook 帧里调用实测导致"僵尸啃咬大蒜瞬间崩溃"（2026-10-16，详见大蒜段注释）。
#define ZOMBIE_ROW_OFFSET 0x130
static int GarlicZombieRow(DWORD z) { return MemSafeRead<int>(z + ZOMBIE_ROW_OFFSET); }

// ★ 大蒜换行唯一核心 = 僵尸换行函数 0x52B7D2 内的 0x52B902 随机分支（反汇编实证）：
//     0x52B902: mov eax,2 ; call 0x5AF400(Rand) ; test eax,eax ; jne UP
//     0x52B910: add [edi+0x1C],1   (随机0 → 向下 行+1)
//     0x52B916: add [edi+0x1C],-1  (随机1 → 向上 行-1)
//     0x52B91A: 重算 [edi+0x20]=行*10000+0x49F9C（图层）
//   该分支执行前，栈上 [esp+0x17]=向上可用(esi=行-1)、[esp+0x16]=向下可用(edx=行+1)。
//   该分支只在"两边都可用"时到达（0x52B8C5 jne）；边上单独可用的情况前面已直接写行号返回，
//   而边上本来就只有唯一方向 —— 与"行约束"语义天然一致，无需额外接管。
//   patch 该 24 字节为 call GarlicPickRow(edi, 上可用, 下可用) → eax=目标行号。
static int g_garlicT1MaxHp = 600;    // GARLIC_T1_MAXHP  1阶起血量上限
static int g_garlicArrowOffX = 34;   // GARLIC_ARROW_OFFSET_X  箭头相对格左上角 X 偏移
static int g_garlicArrowOffY = 52;   // GARLIC_ARROW_OFFSET_Y  箭头相对格左上角 Y 偏移
const int GARLIC_T0_MAXHP = 400;     // 0阶血量上限（=原版进啃咬态初始化值，代码常量）
// 每株当前等阶（血量阶梯回满血判定）
static std::map<DWORD, int> g_garlicCurTier;
// ★ 大蒜方向：d 字段在行号之前就已确定为 GARLIC_DOWN / GARLIC_UP；
//   row5 在之后确定（0~4），且 GarlicDirIsValid(row5,d) 保证它与约束一致（见下）。
enum { GARLIC_DOWN = 0, GARLIC_UP = 1 };
static const int GARLIC_SLOT_NONE = -1;
static const int GARLIC_SLOT_MAX = 64;
struct GarlicSlot { DWORD addr; int id; int dir; };
static GarlicSlot g_garlic[GARLIC_SLOT_MAX];   // 线性表（帧内禁 std::map 插入）
static int  g_garlicCount = 0;
static int  g_garlicCount6 = 0;                // 六行地图上的大蒜株数（统计用）
static bool g_garlicArrowImgLoaded = false;   // 箭头贴图加载标志
static DWORD g_garlicUpImage = 0;             // UpArrow.png（竖直翻转）
static DWORD g_garlicDownImage = 0;           // DownArrow.png
static int  g_garlicRowHookState = 0;         // 0未装 1已装 -1字节不符
static int  g_garlicRowHookTries = 0;
static int  g_garlicSmashHookState = 0;       // 巨人 call 重定向：0未装 1已装 -1字节不符
static int  g_garlicSmashHookTries = 0;
static int  g_garlicPickCalls = 0;            // GarlicPickRow 被调用次数（诊断）
static int  g_garlicRowWrites = 0;            // 成功改写僵尸行号次数（诊断）
static int  g_garlicNoTarget = 0;             // 换行时找不到 2 阶+ 大蒜而回退原版的次数（诊断）
static int  g_garlicEarlyAddr = 0;            // 提前返回：僵尸地址非法（诊断）
static int  g_garlicEarlyRow = 0;             // 提前返回：僵尸行号越界（诊断）
static int  g_garlicEarlyBoard = 0;           // 提前返回：Board 指针为空（诊断）
static int  g_garlicDebug = 0;                // GARLIC_DEBUG=1 → 写 D:\pvz_garlic.log
static int  g_garlicEnabled = 1;              // GARLIC_ENABLED=0 → 整段大蒜机制停用（排障用）

// ==================== 火炬树桩特殊机制 ====================
// 子弹过火状态: 0=normal, 1=weakFire, 2=fire, 3=blaze
struct ProjectileFireState
{
	int fireLevel;    // 0=normal, 1=weakFire(弱火), 2=fire(火), 3=blaze(炎)
	int damage;       // 自定义直伤伤害值
	bool noDefrost;   // 5阶：不消除僵尸减速/冻结效果
	int lastTorchCol; // 上一次过火的火炬树桩列号（-1=未经过，防止同一火炬重复触发）
};
std::map<int, ProjectileFireState> g_projectileFireStates;
// 刚被 onPeaOnFire 处理的子弹（防止同一帧内 onGameObjectsUpdate 重复升级）
std::set<int> g_justFiredProjectiles;
// 火炬树桩过火 hook 延迟安装标志（游戏代码解密完成后）
static bool g_torchwoodHookInstalled = false;

// ==================== 豌豆子弹染色 ====================
// 染色标记存 [proj+0x8C]（Projectile 空闲字段，0x88=TracktargetId / 0x90=Id 之间）：
//   0 = 不染色（普通豌豆/冰豌豆/原生火豌豆）
//   1 = 弱火豌豆（火炬 0-1阶过火，淡橙黄）
//   2 = 炎豌豆（火炬 3阶+ 火→炎升级，炽红）
//   3 = 冰火豌豆（双发 5阶 / 火炬 1阶+ 冰豆过火，冰蓝）
// 染色实现：hook @ 0x46E805（Projectile::Draw 主贴图绘制 push 0072289C 处），
//   按 [ebp+8](子弹)+0x8C 标记替换 DrawImage 颜色指针（参考 S6 CE 表"灵魂子弹颜色"）。
// 颜色数组格式 {R,G,B,A}（与 PVZ::Color 一致，DrawImage 颜色参数指向 4 int）
static int g_peaWeakFireColor[4] = { 0xFF, 0xC8, 0x64, 0xFF };  // 弱火：淡橙黄
static int g_peaBlazeColor[4]    = { 0xFF, 0x40, 0x30, 0xFF };  // 炎：炽红
static int g_peaIceFireColor[4]  = { 0x66, 0xCC, 0xFF, 0xFF };  // 冰火：冰蓝（乘色对橙红火球无效，仅留档）
// 冰火蓝火贴图（make_icefire_png.py 色相旋转生成，存游戏 images/）
// ★ 乘色数学死路：火球贴图橙红(B≈0)，tint 乘色 B 通道恒 0 → 永远出不了蓝（实测变绿）。
//   冰火改用 reanim 轨道 image 覆盖（SetImageOverride 0x473490 同款），弱火/炎保持 tint。
// ★ 2026-09-01 尾焰修复：单帧 override 导致 flames 轨道 3 帧动画静止。
//   改为"按帧匹配换图"：游戏每帧更新轨道元素 +0x40=当前帧原版图 → 匹配后写 +0x44=对应蓝版
//   → 绘制用 override(+0x44) 显示蓝版当前帧 → 火焰恢复动态。匹配表 4 对（主体 + flame1/2/3）。
static DWORD g_iceFireImgPairs[4][2] = { {0, 0}, {0, 0}, {0, 0}, {0, 0} }; // {原版image, 蓝版image}
static int g_iceFireImgPairCount = 0;
static bool g_iceFireImagesLoaded = false;
// 轮询异常计数（__except 排障铁律：空实现是盲区）
static int g_peaTintErr = 0;
// 染色 hook 已安装标志（延迟到 onGameObjectsUpdate 首次执行时安装，同冰锥贴图 hook）
static bool g_peaColorHookInstalled = false;

// 出怪配置延迟应用标志（BoardInitAfter 太早，波次未填充）
static bool g_waveConfigPending = false;

// ==================== 三叶草特殊机制 ====================
// 三叶草是一次性植物：种下后有前摇，前摇期间可接收同行其他植物死亡转移的经验，
// 前摇结束原版自动吹飞飞行僵尸(0阶效果)，植物消失时(onPlantRemove)按自身经验
// 判定等阶并追加 1/2/3 阶效果。各阶效果叠加(高阶含低阶)。
//   1阶: 全屏僵尸减速10s
//   2阶: 全屏僵尸击退(默认40px)
//   3阶: 全屏植物攻速提升(冷却缩减默认33%)持续5s(默认500厘秒)
int g_bloverKnockbackDistance = 40;        // 2阶击退距离(px)
float g_bloverSpeedBoostReduction = 0.33f; // 3阶冷却缩减比例(0~1)
int g_bloverSpeedBoostDuration = 500;      // 3阶增益持续时间(厘秒, 500=5s)
int g_bloverBoostEndTime = 0;              // 3阶增益结束时刻(PlayingTime, 厘秒)；0=无增益
static bool g_bloverHookInstalled = false; // 吹飞时刻 hook 延迟安装标志（游戏代码解密后）
// 吹飞时刻(0x460F4B)只记录三叶草地址，实际触发延迟到 onGameObjectsUpdate：
// 铲同行植物→onPlantRemove 设置的死亡经验要在分配后才轮到三叶草（分配发生在绘制阶段，
// 而吹飞在 Update 阶段早于绘制），延迟一帧触发才能读到正确等阶。
static std::set<int> g_pendingBloverTriggers;

// ==================== 胆小菇特殊机制 ====================
// 渐变攻速：每发射击缩短间隔，每秒不攻击延长间隔
int g_scaredySpeedDownMs = 20;   // 每发缩短间隔（毫秒）
int g_scaredySpeedUpMs = 20;     // 每秒延长间隔（毫秒）

// 胆小菇每株攻速状态
struct ScaredyState
{
	float currentInterval;   // 当前实际攻击间隔（厘秒）
	int lastAttackTime;      // 上次攻击时的PlayingTime（厘秒）
	int lastManualShootTime; // T5手动射击计时（厘秒），用于免疫缩头时的手动开火节拍
	int prevShootingCD;      // 上一帧 ShootingCountdown(0x90)，用于检测新射击动画开始
};

// 胆小菇原版基准：攻速 1.5s=150cs；FindTargetAndFire(0x45F1A1) 固定写 [plant+0x90]=25
const int SCAREDY_BASE_INTERVAL_CS = 150;
std::map<DWORD, ScaredyState> g_scaredyStates;

// ==================== 小喷菇分身系统 ====================
// 设计原则：同一格所有小喷菇地位相同，不区分本体/分身
// plants[0] = 基准位置（无偏移），plants[1-4] = 分身位置（有偏移）
// 经验存在 plants[0] 名下；plants[0] 死亡时提拔下一个为新的 plants[0]
struct PuffshroomCluster
{
	DWORD plants[5] = {0, 0, 0, 0, 0};   // 所有小喷菇地址，0=空，0号位=基准位无偏移
	int lastSpawnTime = 0;                // 上次生成时的 PlayingTime
	int maxCount = 0;                     // 本格最大数量（基于等阶）
	bool clusterAwake = false;            // 本格是否已用咖啡豆唤醒

	int GetCount() const
	{
		int cnt = 0;
		for (int i = 0; i < 5; i++)
			if (plants[i] != 0) cnt++;
		return cnt;
	}

	// 找到低编号空位（0号位始终是"首领"，优先占1-4号位）
	int FindEmptySlot() const
	{
		for (int i = 1; i < 5; i++)
			if (plants[i] == 0) return i;
		return -1;
	}

	void RemovePlant(DWORD addr)
	{
		for (int i = 0; i < 5; i++)
			if (plants[i] == addr) { plants[i] = 0; break; }
	}

	DWORD GetLeader() const { return plants[0]; }
};

// 格子key(row * 10 + col) → 集群
std::map<int, PuffshroomCluster> g_puffClusters;
// 任意小喷菇地址 → 格子key（快速反查，用于显示跳过和经验重定向）
std::map<DWORD, int> g_puffToCell;

// 正在创建额外小喷菇时的标记（防止 onPlantCreate 重复建集群）
static bool g_creatingExtraPuff = false;

// 相对于 plants[0] 的位置偏移（索引 1-4 对应 plants[1-4]）
struct PuffCloneOffset
{
	float dx, dy;         // 相对偏移（像素）
	int layerDelta;       // 图层差（递增：高编号上层→僵尸先攻击→死后原位再生）
};
static const PuffCloneOffset PUFF_CLONE_OFFSETS[4] = {
	{  24.0f, -12.0f, -2 },  // plants[1]: 右上方 (X+24, Y-12)，最下层
	{ -14.0f, -21.0f, -1 },  // plants[2]: 左上方 (X-14, Y-21)，次下层
	{ -26.0f,  14.0f,  1 },  // plants[3]: 左下方 (X-26, Y+14)，次上层
	{  18.0f,  12.0f,  2 },  // plants[4]: 右下方 (X+18, Y+12)，最上层
};

// 根据等阶获取本格最大小喷菇数量
static int GetPuffMaxCount(int tier)
{
	// Tier 0: 1   Tier 1: 2   Tier 2: 3   Tier 3: 3   Tier 4: 4   Tier 5: 5
	if (tier <= 0) return 1;
	if (tier == 1) return 2;
	if (tier == 2) return 3;
	if (tier == 3) return 3;
	if (tier == 4) return 4;
	return 5; // tier 5
}

// 前向声明
static void TryApplyWaveConfig(DWORD boardAddress);
void LoadZombieMechanicsConfig(); // 撑杆司令配置（定义在出怪配置应用段）

// ==================== 出怪配置系统 ====================

// 单波出怪数据
struct WaveData
{
	std::vector<ZombieType::ZombieType> zombies;
};

// 单个关卡的出怪配置
struct LevelWaveConfig
{
	int waveCount;           // -1 = 使用默认
	std::map<int, WaveData> waves; // wave index -> zombies
};

// 全局配置映射: 关卡标识字符串 -> 出怪配置
static std::map<std::string, LevelWaveConfig> g_waveConfigs;

// ==================== 撑杆司令（PoleCommander）全局状态 ====================
// 详细说明见"出怪配置应用"段。核心：waves.ini 写 PoleCommander → 槽位按撑杆僵尸(3)出怪，
// 本 DLL 用框架事件（ZombieInitAfter@0x524035 标记 + PoleVaulter::FullJumpEvent@0x52601B 二段跳）
// 施加 血量/移速/二段跳。★0x52xxxx 僵尸区域运行时解密晚，事件必须延迟到进关后注册。
static float g_polevaulterSpeedMult = 1.5f;           // 移速倍率（zombie_mechanics.ini 可调）
static int g_polevaulterHp = 1000;                    // 血量（zombie_mechanics.ini 可调）
static std::map<int, std::set<int>> g_commanderWaveSlots; // 波次 -> 司令"类型3序号"集合（TryApplyWaveConfig 填充）
static int g_lastSeenWave = -1;                       // onGameObjectsUpdate 每帧对比的波次
static int g_type3SeenInWave = 0;                     // 当前波已见到的类型3僵尸数（波变化时重置）
static std::set<int> g_seenPoleVaulters;              // 本关卡已见过的类型3僵尸（键=僵尸Id+0x158，槽位地址会被复用）
static std::set<int> g_commanderZombies;              // 司令僵尸Id集合
static std::map<int, float> g_cmdrBaseSpeed;          // 司令Id -> 游戏原生持杆跑速（创建时捕获）
static std::map<int, int> g_cmdrJumps;                // 司令Id -> 已完成跳跃次数
static std::map<int, int> g_cmdrLastState;            // 司令Id -> 上一帧状态（落地检测用，轮询版）
static std::map<int, float> g_cmdrPrevX;              // 司令Id -> 上一帧 X（测量法补速用，记录补之前的值）
// 动画实例级"杆子状态"复制：自然持杆跑稳定期快照整个动画实例（0xA0 字节），force 时整块写回
// （tdiff 证实杆子显示状态在动画实例内部；游戏丢杆=重写动画实例内容，单字段/轨道都救不回）
static std::map<int, std::array<BYTE, 0xA0>> g_cmdrAnimSnap; // 司令Id -> 持杆跑动画实例快照
static std::set<int> g_cmdrAnimSnapTaken;                   // 已快照
static std::map<int, int> g_cmdrRunFrames;                  // 司令Id -> 持杆跑持续帧数（延迟快照确保初始化）
// 司令皮肤贴图（只给司令换，普通撑杆保持原版）：
//   0=hair           -> Zombie_polecommander_hair.png           轨道 "anim_hair"（FindTrackIndex=24 已实测）
//   1=body1          -> Zombie_polecommander_body1.png          轨道 Zombie_polevaulter_body1（idx=21 已实测）
//   2=outerarm_upper -> Zombie_polecommander_outerarm_upper.png 轨道 Zombie_polevaulter_outerarm_upper（idx=26 已实测）
//   3=outerarm_upper2-> Zombie_polecommander_outerarm_upper2.png ★无独立轨道！是 upper 轨道的第二张
//                      关键帧贴图（"掉手之后"的无杆走路手臂形态；rdata 只有 IMAGE_..._OUTERARM_UPPER2
//                      图像枚举、无独立轨道名字符串；FindTrackIndex(..._upper2) 返回 0 是"找不到"误匹配；
//                      轨道实例里也没有指向原版贴图的指针字段——指针扫描 kfUpper=0 实测无效）。
//                      → 按状态切换 upper 轨道 override：无杆走路(0xD) 时用 commander_upper2，
//                        持杆/跳跃用 commander_upper（见 ApplyCommanderSkinInner）
static DWORD g_cmdrSkinImages[4] = { 0, 0, 0, 0 };        // 司令皮肤贴图（游戏内 Image*，延迟加载）
static bool g_cmdrSkinImageLoaded = false;                 // 皮肤贴图加载标志（onGameObjectsUpdate 首次执行加载）
// 前向声明（定义在"出怪配置应用"段，onGameObjectsUpdate 之前需可见）
static void MarkPoleCommander(DWORD zombieAddr);
static void UpdatePoleVaulterWaveTracking(DWORD boardAddress);
static void UpdatePoleCommanderFrame(DWORD boardAddress); // 每帧轮询：标记司令 + 移速 + 二段跳
static bool ApplyCommanderSkin(DWORD zombieAddr);        // 给司令换 4 处皮肤贴图（幂等，可每帧调用）
static void LoadCommanderSkinImages();                   // 加载司令皮肤贴图（独立函数，__try 需避开 C2712）

// ==================== 防爆门僵尸（BlastproofDoorZombie）全局状态 ====================
// 自定义僵尸：铁门僵尸(类型6) + 铁桶(头盔) 双防具。铁门（盾牌）存在时，受到的任何伤害
// （子弹/窝瓜/土豆雷/灰烬等，全部走 Zombie::TakeDamage/TakeBodyDamage）限伤 MaxDamagePerHit，
// 只有小推车（LawnMower::MowZombie@0x458540，直接击杀不走伤害结算）能无视该机制。
// 出场链路与撑杆司令一致：waves.ini 写 BlastproofDoorZombie(34) → 槽位按铁门僵尸(6)出怪，
// onGameObjectsUpdate 每帧轮询按"本波第几个类型6"匹配槽位 → 标记并施加配置血量/铁桶贴图。
// 两种防具血量仅对"被标记的防爆门"生效，普通铁桶/铁门僵尸数值不受影响。
static int g_blastDoorHp = 1100;              // 铁门（盾牌）血量（zombie_mechanics.ini 可调）
static int g_blastBucketHp = 1100;            // 铁桶（头盔）血量（zombie_mechanics.ini 可调）
static int g_blastBodyHp = 200;               // 本体血量（zombie_mechanics.ini 可调）
static int g_blastMaxDamage = 200;            // 铁门存在时的单次伤害上限（zombie_mechanics.ini 可调）
static std::map<int, std::set<int>> g_blastWaveSlots;  // 波次 -> 防爆门"类型6序号"集合（TryApplyWaveConfig 填充）
static int g_type6SeenInWave = 0;             // 当前波已见到的类型6僵尸数（波次变化时重置，同撑杆司令计数）
static std::set<int> g_seenType6;             // 本关卡已见过的类型6僵尸（键=僵尸Id+0x158）
static std::set<int> g_blastDoorZombies;      // 防爆门僵尸Id集合（铁门存在时其伤害被限流）
static bool g_blastHooksReady = false;        // 限伤 hook 已成功安装
static bool g_blastHooksGivenUp = false;      // 限伤 hook 安装放弃（运行时字节与预期不符，防刷屏）
static int g_blastHookTries = 0;              // 限伤 hook 安装重试计数
static bool g_blastBurnHookInstalled = false; // ApplyBurn 化灰拦截 hook 安装标志
static int g_blastBurnDmgScratch = 0;         // ApplyBurn trampoline 暂存：限伤伤害值（游戏线程单线程，安全）
static int g_blastBurnEsiScratch = 0;         // ApplyBurn trampoline 暂存：调用方 esi（TakeDamage 会改写 esi）
static bool g_blastChomperHookInstalled = false; // 大嘴花撕咬判定 hook 安装标志（防爆门像巨人一样被撕咬）
static bool g_blastFindHookInstalled = false;    // 大嘴花索敌兜底 hook 安装标志（索敌失败时找防爆门）
static bool g_blastFreedPlantGuardInstalled = false; // 植物数组"已释放对象"防御守卫 hook（0x463920，防 0x463928 崩溃）
static bool g_blastFreedPlantTailGuardInstalled = false; // 同类守卫 · Plant::Update 尾部（0x463ED2，防 0x46441F 崩溃）
static bool g_blastMagnetBlockInstalled = false; // 磁力菇跳过防爆门 hook 安装标志（不能吸防爆门的防具）
static bool g_blastSkipAnimInstalled = false;    // 大嘴花跳过撕咬动画 hook 安装标志（防爆门→直接伤害段，绕开 0x515020 崩溃）
static bool g_blastSkipCallInstalled = false;    // 大嘴花拦截撕咬动画 call hook 安装标志（0x4614D7 直接拦 call 0x515020）
static bool g_nullVtableGuardInstalled = false;  // 容器"空虚表派发"防御守卫 hook（0x565A53，防 0x565A55 崩溃）
static int  g_nullVtableGuardTries = 0;          // 守卫安装重试计数（0x56 区代码可能运行时解密，需逐字节探测）
static bool g_nullVtableGiveUp = false;          // 守卫安装放弃（运行时字节与预期不符，超窗后防刷屏）
// ===== 大嘴花（Chomper, SeedType=6）等阶机制全局 =====
static int  g_chomberBitePercent = 10;           // 5阶撕咬百分比伤害（%）（plant_mechanics.ini 可调）
static std::map<DWORD,int> g_chomberLastState;    // 大嘴花 上一帧 State（消化计时覆盖 + 消化完成回血判定）
static int  g_chomberDigestHeal = 100;           // 每次消化完成回复血量（0-5阶均生效）
static int  g_chomberBiteMinDamage = 40;         // 5阶撕咬百分比伤害保底（低于此取保底）
// 血量上限阶梯（0阶300原版 / 1阶600 / 2阶沿用600 / 3阶1000 / 4阶沿用1000 / 5阶沿用1000）
static const int g_chomperMaxHpLadder[6] = { 300, 600, 600, 1000, 1000, 1000 };
// ★铁门贴图替换（防爆门专用 Blastproof_screendoor1/2/3.png，按铁门血量比例切换）
// 原版铁门轨道 anim_screendoor 的三档贴图（Zombie_screendoor1/2/3）由盾牌伤害处理器
// 0x530BC0 按 ShieldHealth 比例切换（阈值 2Max/3 与 Max/3，反汇编确认）；本数组为
// 防爆门专用替换图（槽位 0=完好 1=一级破损 2=二级破损），每帧 SetImageOverride 幂等覆盖。
static DWORD g_blastDoorImages[3] = { 0, 0, 0 };   // 游戏内 Image*（懒加载）
static bool g_blastDoorImageLoaded = false;          // 3 张贴图全部加载成功标志（失败每帧重试）

// ==================== 磁力菇（MagnetShroom, SeedType=31）等阶机制 ====================
// 需求（2026-10-16 定稿）：
//   磁力菇 3 阶即满阶，可吸取僵尸铁器（原版行为）。
//   · 经验：消化铁器完成时获得「该铁器满耐久(=MaxHealth)」的经验；该僵尸最终死亡结算
//           经验时不再计算这份被吸走的铁器（经验总量守恒）。
//           不作为防具的铁器（跳跳杆/玩偶匣/矿工镐）没有耐久 → 按 0 处理。
//   · 0阶：同原版
//   · 1阶：消化完成时给本行一格上一个 300 耐久护盾（同格多株植物共用一个，不可叠加）。
//          优先无盾格 → 所有格都有盾时给「盾剩余耐久最低」的格重置满 →
//          本行所有格护盾都满耐久则什么都不做；
//          同级优先：格内植物绝对血量最低 → 离磁力菇最近（磁力菇自己最近）→ 靠右。
//   · 2阶：吸铁半径 +90px（原版 270；僵尸正在啃食时 320 → 360 / 410）
//   · 3阶：消化完成时若本行所有格护盾都满耐久 → 把铁器扔给全屏最近的敌人
//          （固定 300 伤害；可打空中气球 / 水中潜水，不可打未出土矿工 / 未低头僵王）；
//          场上没有可索敌敌人 → 一直持有铁器，直到出现可索敌敌人。
//   · 护盾承伤：僵尸啃食先扣护盾；碾压/爆炸等秒杀消耗整个护盾抵挡一次（植物不死）,
//               车类碾压抵挡时同时把车击退一段距离（复用高坚果的击退逻辑）。
//
// hook 点（capstone + IDA 双向核实；入口唯一性已扫全 exe 分支验证）：
//   0x461610 Plant::MagnetShroomAttactItem 入口（ebx=僵尸，栈参=植物）→ 刚吸到铁器
//   0x461E3C UpdateMagnetShroom 内「State==0x1B 且 +0x54==0」的唯一落点 → 消化完成
//            （此刻 [plant+0xD8]=MagnetItem[0].Type 仍有效，0x461F07 才被清零）
//   0x4620F4 吸铁半径取值段（16 字节，无任何外部跳入 → 可整体替换做 2 阶加成）
//   0x52FCF0 Plant::TakeEatDamage（add dword [esi+0x40],-4）→ 啃食伤害拦截
//   秒杀拦截复用高坚果已有三处 hook（0x52E920 / 0x462B80 / 0x527729），
//   判定并入 TallnutAbsorbKill 首段（与大蒜 3 阶免疫同款做法）。
// hook 帧内只做指针读写 + POD 数组线性查找 + 经验表 find（同 ChomperBiteDamage 先例），
// 全部重活（AddPlantExperience / 索敌 / 结算 / 粒子）延迟到每帧轮询帧。

// 护盾按「格」记：同一格多株植物（如花盆上再种一株）共用一个盾
struct MagShieldCell { int row; int col; int hp; };
// 被磁力菇吸走的铁器记录（用于 3 阶扔铁器 + 僵尸死亡结算扣除）
struct MagAbsorbRec
{
	DWORD zombie; int zombieId;
	DWORD magnet; int magnetId; int row;
	int   kind;      // 0=头盔(+0xC4/+0xD4) 1=盾牌(+0xD8/+0xE0) 2=非防具(无耐久,按 0)
	int   maxHp;     // 铁器满耐久 = 经验值 = 死亡结算扣除量
	int   itemType;  // MagnetItemType（飞行贴图用）
	int   digested;  // 1=消化已完成（经验已发或已作废）
	int   expPaid;   // 1=经验确实发给了磁力菇
};
// 消化完成事件（hook 帧只登记 POD，重活留给轮询帧 —— 铁律）
struct MagDigestEvt { DWORD magnet; int magnetId; int row; int itemType; };
// 3 阶「持有中、还没扔出去」的铁器
struct MagHeld { DWORD magnet; int magnetId; int row; int itemType; int kind; int maxHp; };
// 飞行中的铁器（纯表现；伤害在扔出当帧已结算）
struct MagFly
{
	int   active;
	int   itemType;
	DWORD img;
	float x0, y0, x1, y1;
	int   t, dur;
};
// 上盾闪光（在刚上盾的那一格播放「坚果圣盾」并淡出）
struct MagShieldFx { int row; int col; int t; };

static int  g_magShieldHp     = 300;   // MAGNET_SHIELD_HP      护盾耐久
static int  g_magRadiusBonus  = 90;    // MAGNET_RADIUS_BONUS   2阶吸铁半径加成(px)
static int  g_magThrowDamage  = 300;   // MAGNET_THROW_DAMAGE   3阶扔铁器伤害
static int  g_magThrowMs      = 350;   // MAGNET_THROW_MS       飞行总时长(ms)
static int  g_magLadderHp     = 500;   // MAGNET_LADDER_HP      地上梯子耐久(原版 500)

// ★ 贴图偏移：已定稿，硬编码（不再走 ini —— 调好就不再需要外部改了）
//   护盾     images\PlantShield.png      122x156，可见内容 bbox(18,4,113,153)
//   上盾闪光 images\PlantShield_fx*.png   80x83（42-坚果圣盾），整幅不透明
//   闪光偏移由护盾偏移按「两者可见中心重合」反推得出 → 闪光一定落在护盾正中，
//   将来若再微调护盾偏移，闪光偏移按同样的 5px 误差以内跟着改即可。
static const int MAG_SHIELD_OFF_X    = 10;    // 护盾贴图相对「格左上角」X 偏移（实测定稿）
static const int MAG_SHIELD_OFF_Y    = -115;  // 护盾贴图相对「格左上角」Y 偏移（实测定稿）
static const int MAG_SHIELD_FX_OFF_X = 36;    // 上盾闪光 X 偏移（与护盾可见中心重合）
static const int MAG_SHIELD_FX_OFF_Y = -78;   // 上盾闪光 Y 偏移（与护盾可见中心重合）
// 上盾闪光淡出：5 档预烘焙 alpha（100/80/60/40/20），每档 8 逻辑帧 → 总 0.4 秒
static const int MAG_SHIELD_FX_STEPS  = 5;
static const int MAG_SHIELD_FX_FRAMES = 8;

static MagShieldCell g_magShield[64];
static int  g_magShieldCount = 0;
static MagAbsorbRec  g_magAbsorb[128];
static int  g_magAbsorbCount = 0;
static MagDigestEvt  g_magDigestQ[16];
static int  g_magDigestQCount = 0;
static MagHeld       g_magHeld[32];
static int  g_magHeldCount = 0;
static MagFly        g_magFly[16];
static MagShieldFx   g_magShieldFx[8];
static int  g_magShieldFxCount = 0;
static DWORD g_magShieldImg = 0;              // images\PlantShield.png
static DWORD g_magShieldFxImg[MAG_SHIELD_FX_STEPS] = { 0, 0, 0, 0, 0 };   // images\PlantShield_fx100/80/60/40/20.png

// 延迟安装标志（0x46xxxx 立即可装；0x52xxxx 需等运行时解密，逐字节核对）
static bool g_magAbsorbHookInstalled = false;
static bool g_magDigestHookInstalled = false;
static bool g_magRadiusHookInstalled = false;
static bool g_magEatHookInstalled    = false;
static int  g_magEatHookTries        = 0;
static bool g_magEatHookGivenUp      = false;

// 前向声明（实现见"磁力菇等阶机制"段）
static int  __cdecl MagShieldAbsorbKill(DWORD plantAddr);          // 秒杀拦截（并入高坚果入口）
static void MagOnPlantShieldRemoved(DWORD plantAddr);              // onPlantRemove 清理
static void MagFrame(DWORD boardAddress);                          // 每帧轮询（重活）
static void DrawMagnetShields();                                   // DrawUITop 层绘制
static int  MagAbsorbedExpHelm(DWORD zombieAddr);                  // 死亡结算：被吸走的头盔耐久
static int  MagAbsorbedExpShield(DWORD zombieAddr);                // 死亡结算：被吸走的盾牌耐久
static void MagForgetZombie(DWORD zombieAddr);                     // onZombieRemove 清理

// 前向声明（定义在"出怪配置应用"段）
static void MarkBlastproofDoor(DWORD zombieAddr);
static void UpdateBlastproofDoorFrame(DWORD boardAddress);   // 每帧轮询：标记防爆门 + 铁桶贴图
static void LoadBlastDoorImages();                           // 加载 3 张铁门替换贴图（独立函数，__try 避开 C2712）
static void ApplyBlastDoorTexture(DWORD zombieAddr);         // 每帧设置铁门替换贴图（按血量比例选图）
static int __cdecl CapBlastDoorDamage(DWORD zombieAddr, int damage); // 限伤核心（trampoline 直接 call）
static int __cdecl BlastBurnCheck(DWORD zombieAddr);         // ApplyBurn 化灰拦截判定（trampoline 直接 call）
static bool InstallBlastDamageHooks();        // 安装 TakeDamage/TakeBodyDamage 限伤 hook（含运行时字节探测）
static bool InstallBlastBurnHook();           // 安装 ApplyBurn 化灰拦截 hook（含运行时字节探测）
static bool InstallBlastChomperHook();        // 安装大嘴花撕咬 hook（防爆门→0x461451 强制 dl=1 巨人式撕咬）
static bool InstallBlastFreedPlantGuard();    // 安装植物数组已释放对象防御守卫（0x463920）
static bool InstallBlastFreedPlantTailGuard();// 安装植物数组已释放对象防御守卫 · Plant::Update 尾部（0x463ED2，防 0x46441F 崩溃）
static bool InstallNullVtableDispatchGuard(); // 安装容器"空虚表派发"防御守卫（0x565A53，防 0x565A55 崩溃）
static bool InstallBlastFindHook();           // 安装大嘴花索敌兜底 hook（索敌失败时找防爆门）
static bool InstallBlastMagnetBlockHook();    // 安装磁力菇跳过防爆门 hook（0x4620BD，防爆门不参与吸取）
static bool InstallBlastSkipAnimHook();       // 安装大嘴花跳过撕咬动画 hook（0x461490，绕开 0x515020 崩溃）
static bool InstallBlastSkipCallHook();       // 安装大嘴花拦截撕咬动画 call hook（0x4614D7，直接拦 call 0x515020）
static int  __cdecl ChomperBiteDamage(DWORD plantAddr, DWORD zombieAddr); // 大嘴花撕咬伤害（0-4阶=40；5阶=10%封顶200）
static int  __cdecl ChomperShouldBiteOverride(DWORD plantAddr, DWORD zombieAddr, int type); // 防爆门/5阶巨人→走自研撕咬
static void ChomperFrame(DWORD boardAddress);   // 每帧轮询：血量上限 + 消化计时覆盖 + 消化完成回血

// 僵尸英文名 -> ZombieType 映射表
static std::map<std::string, ZombieType::ZombieType> g_zombieNameMap;

// 初始化僵尸名称映射
void InitZombieNameMap()
{
	if (!g_zombieNameMap.empty()) return;
	g_zombieNameMap["Zombie"] = ZombieType::Zombie;
	g_zombieNameMap["FlagZombie"] = ZombieType::FlagZombie;
	g_zombieNameMap["ConeheadZombie"] = ZombieType::ConeheadZombie;
	g_zombieNameMap["PoleVaultingZombie"] = ZombieType::PoleVaultingZombie;
	g_zombieNameMap["BucketheadZombie"] = ZombieType::BucketheadZombie;
	g_zombieNameMap["NewspaperZombie"] = ZombieType::NewspaperZombie;
	g_zombieNameMap["ScreenDoorZombie"] = ZombieType::ScreenDoorZombie;
	g_zombieNameMap["FootballZombie"] = ZombieType::FootballZombie;
	g_zombieNameMap["DancingZombie"] = ZombieType::DancingZombie;
	g_zombieNameMap["BackupDancer"] = ZombieType::BackupDancer;
	g_zombieNameMap["DuckyTubeZombie"] = ZombieType::DuckyTubeZombie;
	g_zombieNameMap["SnorkedZombie"] = ZombieType::SnorkedZombie;
	g_zombieNameMap["Zomboin"] = ZombieType::Zomboin;
	g_zombieNameMap["ZombieBobsledTeam"] = ZombieType::ZombieBobsledTeam;
	g_zombieNameMap["DolphinRiderZombie"] = ZombieType::DolphinRiderZombie;
	g_zombieNameMap["JackintheboxZombie"] = ZombieType::JackintheboxZombie;
	g_zombieNameMap["BalloonZombie"] = ZombieType::BalloonZombie;
	g_zombieNameMap["DiggerZombie"] = ZombieType::DiggerZombie;
	g_zombieNameMap["PogoZombie"] = ZombieType::PogoZombie;
	g_zombieNameMap["ZombieYeti"] = ZombieType::ZombieYeti;
	g_zombieNameMap["BungeeZombie"] = ZombieType::BungeeZombie;
	g_zombieNameMap["LadderZombie"] = ZombieType::LadderZombie;
	g_zombieNameMap["CatapultZombie"] = ZombieType::CatapultZombie;
	g_zombieNameMap["Gargantuar"] = ZombieType::Gargantuar;
	g_zombieNameMap["Imp"] = ZombieType::Imp;
	g_zombieNameMap["DrZomboss"] = ZombieType::DrZomboss;
	g_zombieNameMap["Gigagargantuar"] = ZombieType::Gigagargantuar;
	g_zombieNameMap["PoleCommander"] = ZombieType::PoleCommanderZombie; // 撑杆司令（自定义）
	g_zombieNameMap["BlastproofDoorZombie"] = ZombieType::BlastproofDoorZombie; // 防爆门僵尸（自定义）
}

// 去除字符串首尾空格和回车
static std::string TrimString(const std::string& s)
{
	size_t start = s.find_first_not_of(" \t\r\n");
	if (start == std::string::npos) return "";
	size_t end = s.find_last_not_of(" \t\r\n");
	return s.substr(start, end - start + 1);
}

// 加载 waves.ini 配置文件
void LoadWaveConfig()
{
	g_waveConfigs.clear();
	InitZombieNameMap();

	std::ifstream file("waves.ini");
	if (!file.is_open()) return; // 文件不存在则全部使用默认

	std::string line;
	std::string currentSection; // 当前节名

	while (std::getline(file, line))
	{
		std::string trimmed = TrimString(line);

		// 跳过空行和注释
		if (trimmed.empty() || trimmed[0] == ';' || trimmed[0] == '#')
			continue;

		// 解析节名 [SectionName]
		if (trimmed[0] == '[' && trimmed.back() == ']')
		{
			currentSection = trimmed.substr(1, trimmed.size() - 2);
			currentSection = TrimString(currentSection);
			continue;
		}

		// 必须在某个节内
		if (currentSection.empty()) continue;

		// 解析 Key = Value
		size_t eqPos = trimmed.find('=');
		if (eqPos == std::string::npos) continue;

		std::string key = TrimString(trimmed.substr(0, eqPos));
		std::string value = TrimString(trimmed.substr(eqPos + 1));

		if (key == "WaveCount")
		{
			g_waveConfigs[currentSection].waveCount = SafeAtoiLog(value.c_str(), currentSection.c_str());
		}
		else if (key.substr(0, 4) == "Wave")
		{
			int waveIndex = SafeAtoi(key.substr(4).c_str());
			WaveData wd;
			// 按逗号分割僵尸名
			std::string token;
			std::istringstream tokenStream(value);
			while (std::getline(tokenStream, token, ','))
			{
				std::string zname = TrimString(token);
				auto it = g_zombieNameMap.find(zname);
				if (it != g_zombieNameMap.end())
				{
					wd.zombies.push_back(it->second);
				}
			}
			if (!wd.zombies.empty())
			{
				g_waveConfigs[currentSection].waves[waveIndex] = wd;
			}
		}
	}
}

// 构建当前关卡的标识字符串
static std::string MakeLevelKey(PVZ::Board& board)
{
	PVZ::PVZApp app = board.GetPVZApp();
	PVZLevel::PVZLevel levelId = app.LevelId;

	if (levelId == PVZLevel::Adventure)
	{
		// 冒险模式: "Adventure:N"
		int advLevel = board.AdventureLevel;
		char buf[32];
		sprintf_s(buf, "Adventure:%d", advLevel);
		return std::string(buf);
	}
	else
	{
		// 其他模式: 使用 PVZLevel 的字符串形式
		return PVZLevel::ToString(levelId);
	}
}

// 导出当前关卡的出怪配置到文件（用于收集参考数据）
// boardAddr: 传入的 Board 地址，避免用 PVZ::GetBoard() 读取全局指针（可能未更新）
void ExportCurrentLevelWaves(const char* filename, DWORD boardAddr)
{
	PVZ::Board board(boardAddr);
	if (!board.GetBaseAddress()) return;

	std::string levelKey = MakeLevelKey(board);

	// 二周目导出时自动加 Adventrue2 前缀
	PVZ::PVZApp app = board.GetPVZApp();
	if (app.GetBaseAddress() && app.LevelId == PVZLevel::Adventure)
	{
		PVZ::SaveData sd = PVZ::GetSaveData();
		if (sd.GetBaseAddress() && sd.AdventureFinishCount >= 1)
		{
			levelKey = "Adventure2:" + levelKey.substr(levelKey.find(':') + 1);
		}
	}

	std::ofstream file(filename, std::ios::app);
	if (!file.is_open()) return;

	file << "[" << levelKey << "]" << std::endl;

	int wc = board.WaveCount;
	file << "WaveCount = " << wc << std::endl;

	for (int i = 0; i < wc; i++)
	{
		PVZ::Wave w = board.GetWave(i);
		ZombieType::ZombieType ztypes[50];
		w.GetAll(ztypes);
		int count = w.Count;

		file << "Wave" << i << " = ";
		for (int j = 0; j < count; j++)
		{
			if (j > 0) file << ", ";
			// 尝试输出僵尸名（反向查找）
			bool found = false;
			for (auto& pair : g_zombieNameMap)
			{
				if (pair.second == ztypes[j])
				{
					file << pair.first;
					found = true;
					break;
				}
			}
			if (!found) file << (int)ztypes[j];
		}
		file << std::endl;
	}
	file << std::endl;
	file.close();
}

// ==================== 辅助函数 ====================

// 解析一行阈值字符串 "3000,250,800,1500,2200,3000" → array<int,6>
bool ParseTierThresholds(const std::string& str, std::array<int, 6>& out)
{
	int values[6] = {};
	int count = 0;
	std::string token;
	std::istringstream tokenStream(str);
	while (std::getline(tokenStream, token, ',') && count < 6)
	{
		// 去除前后空格
		size_t start = token.find_first_not_of(" \t");
		size_t end = token.find_last_not_of(" \t");
		if (start == std::string::npos)
			break;
		token = token.substr(start, end - start + 1);
		values[count++] = SafeAtoi(token.c_str());
	}
	if (count == 6)
	{
		for (int i = 0; i < 6; i++)
			out[i] = values[i];
		return true;
	}
	return false;
}

// 加载植物等阶配置文件
void LoadPlantTierConfig()
{
	g_seedTierThresholds.clear();

	std::ifstream file("plant_tier.ini");
	if (!file.is_open())
	{
		// 文件不存在，使用默认配置
		g_seedTierThresholds[-1] = DEFAULT_TIER;
		return;
	}

	std::string line;
	while (std::getline(file, line))
	{
		if (line.empty() || line[0] == ';' || line[0] == '#')
			continue;

		size_t eqPos = line.find('=');
		if (eqPos == std::string::npos)
			continue;

		std::string key = line.substr(0, eqPos);
		std::string value = line.substr(eqPos + 1);

		// 去除 key 前后空格
		size_t kStart = key.find_first_not_of(" \t");
		size_t kEnd = key.find_last_not_of(" \t");
		if (kStart == std::string::npos)
			continue;
		key = key.substr(kStart, kEnd - kStart + 1);

		std::array<int, 6> thresholds;
		if (!ParseTierThresholds(value, thresholds))
			continue;

		if (key == "DEFAULT")
		{
			g_seedTierThresholds[-1] = thresholds;
		}
		else
		{
			int seedType = SafeAtoi(key.c_str());
			g_seedTierThresholds[seedType] = thresholds;
		}
	}
	file.close();

	// 确保默认配置存在
	if (g_seedTierThresholds.find(-1) == g_seedTierThresholds.end())
		g_seedTierThresholds[-1] = DEFAULT_TIER;
}

// 获取种子类型的等阶阈值数组
const std::array<int, 6>& GetSeedTierThresholds(int seedType)
{
	auto it = g_seedTierThresholds.find(seedType);
	if (it != g_seedTierThresholds.end())
		return it->second;

	auto defaultIt = g_seedTierThresholds.find(-1);
	if (defaultIt != g_seedTierThresholds.end())
		return defaultIt->second;

	return DEFAULT_TIER;
}

// 计算植物当前等阶 (0-5)
int GetPlantTier(int seedType, int exp)
{
	const auto& t = GetSeedTierThresholds(seedType);
	// t[0]=MaxExp, t[1]=T1, t[2]=T2, t[3]=T3, t[4]=T4, t[5]=T5
	int tier;
	if (exp < t[1])  tier = 0;   // [0, T1)
	else if (exp < t[2])  tier = 1;   // [T1, T2)
	else if (exp < t[3])  tier = 2;   // [T2, T3)
	else if (exp < t[4])  tier = 3;   // [T3, T4)
	else if (exp < t[5])  tier = 4;   // [T4, T5)
	else tier = 5;               // [T5, MaxExp] 满阶

	// 三阶即满阶植物（配置特征 T4阈值<=T3阈值，如樱桃/辣椒/三叶草/保护伞）：
	// 到达 T3 即满阶，等阶封顶为 3 并按满阶金色绘制（不再显示 Lv.4/Lv.5）
	if (tier > 3 && t[4] <= t[3])
		tier = 3;
	return tier;
}

int GetSeedExperienceLimit(int seedType)
{
	// 优先从等阶配置获取经验上限（T5阈值 = 满阶经验）
	const auto& t = GetSeedTierThresholds(seedType);
	return t[0];
}

// ==================== 西瓜投手升级路线选择（3阶卡点 + 右键选择窗口）====================
// 设计（2026-09-08）：
//   西瓜投手(SeedType 39)经验达到 T3 阈值（plant_tier.ini 39 行第 4 个数，默认 1500）时：
//   ① 底部字幕条提示"你的一株西瓜投手已经达到N经验，试试右击它吧"（每株只提示一次）
//   ② 等阶压制在 2（等阶显示/攻速），直到玩家右键该西瓜打开选择窗口并点击"方案一/方案二"
//   ③ 选择窗口：images\ChooseUpgradeDirection.png(303x600) 从屏幕左侧滑入（纵向满窗口）；
//     面板坐标系 (140,170) 创建西瓜待机动画、(140,420) 创建冰瓜待机动画，
//     动画以面板为参照物跟随滑动（每帧写 reanim mX/mY）
//   ④ 屏幕右下方（窗口外）两个按钮"方案一/方案二"；点击任意按钮 → 面板+动画整体向左滑出，
//     西瓜投手按所选路线解锁升级（路线记录在 g_melSlots，具体路线机制后续版本实现）
// 渲染方案（层级问题的解法）：
//   面板/按钮/文字画在 DrawUITop（屏幕空间最顶层）；两个 reanim 的全部轨道渲染组改为 7，
//   世界通道（Board::Draw 0x4172A7 只 DrawRenderGroup(0,g)）画不到它们 → 世界通道隐身；
//   再在 DrawUITop 里面板之后手动 DrawRenderGroup(7,g)（0x472E40）画在面板上层。
//   由此实现"面板在下、动画在上"且动画跟随面板滑动。
// 安全：
//   待选/已通知/路线状态用 POD 数组 + 线性查找（崩溃铁律：帧内禁 std::map 插入）；
//   跨关清理只清状态不杀 reanim（reanim 随关卡销毁，杀悬空地址=use-after-free）；
//   绘制路径套 __try（同 DrawExpPouchUI 模式）。
// ★槽位身份 = 地址 + 植物 Id(+0x148) 双重校验：植物对象是内存池复用的，
//   铲掉/死亡的西瓜槽位若只按地址匹配，新种的西瓜会继承旧槽位的 route/notified
//   → 直接跳过选择窗自动升阶（实测 bug）。Id 由游戏递增分配，复用地址必换 Id。
struct MelonPendingSlot { DWORD addr; int id; int notified; int route; };   // route: 0=未选 1/2=方案一/二
static MelonPendingSlot g_melSlots[32];
static int g_melSlotCount = 0;

// ==== 布局/速度常量（定稿值，不再走 ini）====
static int MEL_ANIM_X = 120;      // 动画锚点 X（相对面板左上角，定稿）
static int MEL_ANIM1_Y = 110;     // 西瓜锚点 Y（定稿）
static int MEL_ANIM2_Y = 360;     // 冰瓜锚点 Y（定稿）
static int MEL_BTN_X = 300;       // 按钮区 X（屏幕坐标，定稿）
static int MEL_BTN1_Y = 494;      // 方案A按钮 Y（定稿）
static int MEL_BTN2_Y = 548;      // 方案B按钮 Y（定稿）
static int MEL_BTN_W = 163;       // 按钮宽（=左帽36 + 中段46×2 + 右帽35，DrawImage 不支持缩放）
static int MEL_BTN_H = 46;        // 按钮高（贴图原始高度）
static int MEL_TEXT1_X = 50;      // 说明文字A（"A：极致的输出"）X（屏幕坐标，定稿）
static int MEL_TEXT1_Y = 250;     // 说明文字A Y（定稿）
static int MEL_TEXT2_X = 50;      // 说明文字B（"B：强大的群控"）X（定稿）
static int MEL_TEXT2_Y = 500;     // 说明文字B Y（定稿）
static int MEL_SLIDE_STEP = 12;   // 每渲染帧滑动像素（约 25 帧滑满 303px）
static int MEL_BANNER_Y_OFFSET = 135;  // 消息横幅下移像素（定稿；样式12基准Y=0x12C=300，见 MessageWidget::Draw）
static const int MEL_PANEL_W = 303;   // 面板宽（ChooseUpgradeDirection.png 原始尺寸）

static bool g_melUIActive = false;        // 选择窗口激活（滑入/停留/滑出全程）
static int  g_melPhase = 0;               // 0=无 1=滑入 2=停留 3=滑出
static int  g_melSlideX = -MEL_PANEL_W;   // 当前面板 X 偏移（负=屏外）
static DWORD g_melPlantAddr = 0;          // 待选择的西瓜植物地址
static DWORD g_melBoardAddr = 0;          // 开窗时的 Board（换关即作废，防 reanim 悬空引用）
static DWORD g_melReanimMelon = 0;        // 西瓜待机 reanim 地址（AnimationType::Melonpult）
static DWORD g_melReanimWinter = 0;       // 冰瓜待机 reanim 地址（AnimationType::WinterMelon）
static bool  g_melImagesLoaded = false;   // 面板图加载标志（首次绘制前加载）
static DWORD g_melPanelImage = 0;         // ChooseUpgradeDirection.png
// 文字贴图（方案A/B 按钮字 + 两条说明文字；缺图回退 GBK 文字绘制）
static DWORD g_melBtnTextA = 0;           // images\RouteBtnA.png
static DWORD g_melBtnTextB = 0;           // images\RouteBtnB.png
static DWORD g_melTextDescA = 0;          // images\ChooseDescA.png
static DWORD g_melTextDescB = 0;          // images\ChooseDescB.png
// 三块式按钮贴图（原版对话框按钮切片：左帽36 + 中段46平铺 + 右帽35，高46）
static DWORD g_melBtnL = 0, g_melBtnM = 0, g_melBtnR = 0;               // button_left/middle/right.png
static DWORD g_melBtnDownL = 0, g_melBtnDownM = 0, g_melBtnDownR = 0;   // button_down_*（选中/按下态）
static const char g_melIdleTrack[] = "anim_idle";   // 两个 reanim 共用的待机轨道名

// 方案B（冰瓜路线）替换暂存：点击后滑出收场，在帧更新里执行（向日葵→双子同款流程）
static DWORD g_melPendingReplaceAddr = 0;   // 待替换的西瓜投手地址
static int   g_melPendingRow = -1, g_melPendingCol = -1, g_melPendingExp = 0;
static DWORD g_melPendingBoardAddr = 0;     // 方案B暂存发生时的 Board（换关即作废，防地址复用误替换）

// 前向声明（实现统一在"西瓜投手升级路线选择：实现"段，MgCreateReanim/MgKillReanim 之后）
static int   MelonGetSlot(DWORD plantAddr);
static int   MelonGetRoute(DWORD plantAddr);
static bool  MelonHeld(DWORD plantAddr, int seedType);
static int   MelonClampTier(DWORD plantAddr, int seedType, int tier);
static void  MelonResetAll();
static void  MelonShowAdvice(DWORD boardAddr, const char* gbkText);
static void  MelonOnRightClick(DWORD plantAddr, DWORD boardAddr);
static void  DrawMelonChooseUI();
static void  UpdateMelonChooseFrame(DWORD boardAddr);
static int   HandleMelonChooserMouseDown(DWORD boardAddr, int x, int y);
static void  MelonKillChooser(DWORD boardAddr);

// ===== 大蒜（Garlic）机制前向声明（定义见"大蒜等阶机制"段）=====
static int   GarlicOnRightClick(DWORD plantAddr, DWORD boardAddr);
static void  DrawGarlicArrows();

// 植物当前 Id（+0x148，不可读 = 0）
static int MelonPlantId(DWORD plantAddr)
{
	if (plantAddr < 0x10000 || !CrashIsReadable(plantAddr + 0x148, 4))
		return 0;
	return MemSafeRead<int>(plantAddr + 0x148);
}

// 路线查询（未记录 = 0）；地址 + Id 双重匹配，防内存池复用串档
int MelonGetRoute(DWORD plantAddr)
{
	int id = MelonPlantId(plantAddr);
	for (int i = 0; i < g_melSlotCount; i++)
		if (g_melSlots[i].addr == plantAddr && g_melSlots[i].id == id)
			return g_melSlots[i].route;
	return 0;
}

// 获取或创建槽位（满则返回 -1）；地址 + Id 双重匹配
int MelonGetSlot(DWORD plantAddr)
{
	int id = MelonPlantId(plantAddr);
	for (int i = 0; i < g_melSlotCount; i++)
		if (g_melSlots[i].addr == plantAddr && g_melSlots[i].id == id)
			return i;
	if (g_melSlotCount >= 32) return -1;
	g_melSlots[g_melSlotCount].addr = plantAddr;
	g_melSlots[g_melSlotCount].id = id;
	g_melSlots[g_melSlotCount].notified = 0;
	g_melSlots[g_melSlotCount].route = 0;
	return g_melSlotCount++;
}

// 剪枝：删掉"场上已无对应活西瓜"的槽位（死亡/铲除/地址复用全场景）。
// 每帧在扫描前调用——植物对象地址会被内存池复用，死槽位不删会污染新西瓜
// （继承 route → 跳过选择窗自动升阶；继承 notified → 永不提示）。
static void MelonPruneSlots(int plantArray, int plantCount)
{
	for (int i = g_melSlotCount - 1; i >= 0; i--)
	{
		bool alive = false;
		for (int j = 0; j < plantCount; j++)
		{
			DWORD p = plantArray + j * 0x14C;
			if (p != g_melSlots[i].addr) continue;
			if (MemSafeRead<BYTE>(p + 0x141)) continue;              // NotExist
			if (MemSafeRead<int>(p + 0x24) != (int)SeedType::Melonpult) continue;
			if (MelonPlantId(p) != g_melSlots[i].id) continue;                   // 地址被复用给新西瓜
			alive = true;
			break;
		}
		if (!alive)
		{
			g_melSlots[i] = g_melSlots[g_melSlotCount - 1];   // swap-delete
			g_melSlotCount--;
		}
	}
}

// 西瓜是否处于"卡 3 阶待选择"状态（经验 >= T3 且未选路线）
bool MelonHeld(DWORD plantAddr, int seedType)
{
	if (seedType != (int)SeedType::Melonpult) return false;
	if (MelonGetRoute(plantAddr) != 0) return false;
	auto it = g_plantExperience.find(plantAddr);
	int exp = (it != g_plantExperience.end()) ? it->second : 0;
	const auto& t = GetSeedTierThresholds(seedType);
	return exp >= t[3];
}

// 等阶夹紧：卡点中的西瓜按 2 阶参与等阶显示/攻速（选完路线即解锁真实等阶）
int MelonClampTier(DWORD plantAddr, int seedType, int tier)
{
	if (tier > 2 && MelonHeld(plantAddr, seedType))
		return 2;
	return tier;
}

void MelonResetAll()
{
	g_melSlotCount = 0;
	memset(g_melSlots, 0, sizeof(g_melSlots));
	g_melPendingReplaceAddr = 0;
	g_melPendingRow = -1;
	g_melPendingCol = -1;
	g_melPendingExp = 0;
	g_melPendingBoardAddr = 0;
}

// 画文字前强制设置大字体（样式12 → [0x6A7714]，MessageWidget::GetFont 0x459990 表驱动）。
// ★每次绘制文字前都要重设：中间任何游戏绘制调用都可能改写 g+0x40。
static void MelonSetFont(DWORD g)
{
	int bannerFont = MemSafeRead<int>(0x6A7714);
	if (bannerFont >= 0x10000 && CrashIsReadable(g + 0x40, 4))
		MemSafeWrite<int>(g + 0x40, bannerFont);
}

// ==================== 升级路径选择（跨植物通用，供存档系统调用）====================
// "选路线升级"机制：植物经验达 N 阶阈值时停升并让玩家选路线，选完才继续解锁真实等阶。
//   - 西瓜投手：路线A=保持西瓜，路线B=变冰瓜（Remove+CreatePlant 替换，经验全转移）
//   - ★未来杨桃等：同样是选路线机制，但两种路线是同一株植物（仅属性/行为不同）
// 本组函数按 seedType 分发到各植物的路线表，存档/还原只认 route(0=未选 1/2=已选)，
// 与植物类型解耦 → 杨桃等新植物只需在此补一个分支即可复用存档！
// （MelonGetSlot/MelonGetRoute 已在前文前置声明）

// 查询某株植物已选路线（无路线机制或未选 = 0）
static int PlantPathGetRoute(int seedType, DWORD plantAddr)
{
	if (seedType == (int)SeedType::Melonpult)
		return MelonGetRoute(plantAddr);
	// 未来杨桃等（两路径同一株）：if (seedType == (int)SeedType::Starfruit) return StarfruitGetRoute(plantAddr);
	return 0;
}

// 还原某株植物已选路线（读档后把路线写回该植物地址对应的路线表）
static void PlantPathRestoreRoute(int seedType, DWORD plantAddr, int route)
{
	if (route <= 0)
		return;   // 未选 / 无路线机制：不注册（保持"卡点待选"的原生状态）
	if (seedType == (int)SeedType::Melonpult)
	{
		int s = MelonGetSlot(plantAddr);
		if (s >= 0)
			g_melSlots[s].route = route;
	}
	// 未来杨桃等：if (seedType == (int)SeedType::Starfruit) StarfruitSetRoute(plantAddr, route);
}

// 解析浮点阈值字符串 "1.5,1.3,1.2,1.2,1.0,1.0" → array<float,6>
bool ParseAttackSpeeds(const std::string& str, std::array<float, 6>& out)
{
	float values[6] = {};
	int count = 0;
	std::string token;
	std::istringstream tokenStream(str);
	while (std::getline(tokenStream, token, ',') && count < 6)
	{
		size_t start = token.find_first_not_of(" \t");
		size_t end = token.find_last_not_of(" \t");
		if (start == std::string::npos)
			break;
		token = token.substr(start, end - start + 1);
		values[count++] = SafeAtof(token.c_str());
	}
	if (count == 6)
	{
		for (int i = 0; i < 6; i++)
			out[i] = values[i];
		return true;
	}
	return false;
}

// 加载植物等阶攻速配置文件
void LoadPlantAttackSpeedConfig()
{
	g_seedAttackSpeeds.clear();

	std::ifstream file("plant_attack_speed.ini");
	if (!file.is_open())
	{
		g_seedAttackSpeeds[-1] = DEFAULT_ATTACK_SPEED;
		return;
	}

	std::string line;
	while (std::getline(file, line))
	{
		if (line.empty() || line[0] == ';' || line[0] == '#')
			continue;

		size_t eqPos = line.find('=');
		if (eqPos == std::string::npos)
			continue;

		std::string key = line.substr(0, eqPos);
		std::string value = line.substr(eqPos + 1);

		size_t kStart = key.find_first_not_of(" \t");
		size_t kEnd = key.find_last_not_of(" \t");
		if (kStart == std::string::npos)
			continue;
		key = key.substr(kStart, kEnd - kStart + 1);

		std::array<float, 6> speeds;
		if (!ParseAttackSpeeds(value, speeds))
			continue;

		if (key == "DEFAULT")
			g_seedAttackSpeeds[-1] = speeds;
		else
		{
			int seedType = SafeAtoi(key.c_str());
			g_seedAttackSpeeds[seedType] = speeds;
		}
	}
	file.close();

	if (g_seedAttackSpeeds.find(-1) == g_seedAttackSpeeds.end())
		g_seedAttackSpeeds[-1] = DEFAULT_ATTACK_SPEED;
}

// 获取植物在指定等阶下的攻击速度（秒）
float GetPlantAttackSpeed(int seedType, int tier)
{
	if (tier < 0) tier = 0;
	if (tier > 5) tier = 5;

	auto it = g_seedAttackSpeeds.find(seedType);
	if (it != g_seedAttackSpeeds.end())
		return it->second[tier];

	auto defaultIt = g_seedAttackSpeeds.find(-1);
	if (defaultIt != g_seedAttackSpeeds.end())
		return defaultIt->second[tier];

	return DEFAULT_ATTACK_SPEED[tier];
}

// ==================== 金盏花（Marigold）配置与全局状态 ====================
// 完整机制说明见"金盏花（Marigold）形态产出物机制"段（函数实现处）。
// ★ 这些声明必须早于 LoadPlantMechanicsConfig / 鼠标处理（全局可访问，仅此一处）。
#define MG_MAX_PLANTS 48
#define MG_MAX_ITEMS  96
#define MG_MAX_SPRAYS 16
#define MG_MAX_BOOSTS 48

// 金盏花形态记录（POD 数组，produce hook 帧内安全线性查找）
struct MgPlantRec { DWORD plant; int form; int lastTint; DWORD lastReanim; };   // lastTint=已涂形态, lastReanim=已处理的 reanim 地址
static MgPlantRec g_mgPlants[MG_MAX_PLANTS];
static int g_mgPlantCount = 0;

// 产出物（type: 0肥料 1水壶 2留声机 3杀虫剂）
// ★ 每个物品自带独立生命周期（spawnCs=产出时刻, lifeCs=到下次产出的时长）。
//   不能用"实时读植物产出倒计时 [plant+0x58]"判断渐隐/销毁——玩家拾起物品（选中=豁免）
//   再取消选中后，倒计时窗口早已过去，物品会一直保留到下次产出才被清掉（时有时无 BUG）。
struct MgItemRec { DWORD plant; int type; int serial; int spawnCs; int lifeCs; };
static MgItemRec g_mgItems[MG_MAX_ITEMS];
static int g_mgItemCount = 0;
static int g_mgSelected = -1;          // 选中的产出物下标，-1=无
static int g_mgItemSerial = 0;         // 产出物全局序号（顶替最旧用）

// 杀虫剂区域
struct MgSprayRec { int row, col; DWORD source; int startCs; int ticks; };
static MgSprayRec g_mgSprays[MG_MAX_SPRAYS];
static int g_mgSprayCount = 0;

// 留声机攻速加成
struct MgBoostRec { DWORD plant; int endCs; };
static MgBoostRec g_mgBoosts[MG_MAX_BOOSTS];
static int g_mgBoostCount = 0;

// 配置（plant_mechanics.ini 可调）
static int g_mgWaterHeal = 300;        // 水壶回血量
static int g_mgBoostPercent = 40;      // 留声机攻速加成百分比（默认40%=提速1.67倍）
static int g_mgBoostDurationCs = 800;  // 留声机持续（厘秒，8秒）
static int g_mgSprayDps = 50;          // 杀虫剂每秒伤害（真伤）
static int g_mgSprayDurationCs = 500;  // 杀虫剂持续（厘秒，5秒）
static int g_mgItemMax = 3;            // 每株金盏花最多产出物（兼容保留：现行为每次产出销毁旧物品，此值仅作历史配置项）
static int g_mgProduceIntervalCs = 0;  // 金盏花产出间隔（厘秒，0=原版约24秒）

static bool g_mgHookInstalled = false;      // 0x45FB1D 产出 hook 安装标志
static bool g_mgImagesLoaded = false;       // 产出物图片加载标志
static DWORD g_mgImgFertilizer = 0;         // Fertilizer.png
static DWORD g_mgImgWater = 0;              // WateringCan.png
static DWORD g_mgImgPhono = 0;              // Phonograph.png
static DWORD g_mgImgSpray = 0;              // bug_spray.png
// 产出物渐隐 alpha 档位图（a50=半透明 / a25=更透明）
static DWORD g_mgImgFertA50 = 0, g_mgImgFertA25 = 0;
static DWORD g_mgImgWaterA50 = 0, g_mgImgWaterA25 = 0;
static DWORD g_mgImgPhonoA50 = 0, g_mgImgPhonoA25 = 0;
static DWORD g_mgImgSprayA50 = 0, g_mgImgSprayA25 = 0;
// 金盏花花瓣染色图（Marigold_petals 轨道替换用）+ 原图（恢复用）
static DWORD g_mgImgPetalsOrig = 0;
static DWORD g_mgImgPetalsBlue = 0;
static DWORD g_mgImgPetalsYellow = 0;
static DWORD g_mgImgPetalsGreen = 0;
static int g_mgPrevRB = 0;                  // 右键沿检测

// 使用效果动画（水壶/肥料/留声机/杀虫剂 reanim）定时清理记录
struct MgFxAnim { DWORD addr; int endCs; };
static MgFxAnim g_mgFxAnims[16];
static int g_mgFxCount = 0;

// ==================== 玉米投手（KernelPult, SeedType=34）机制 ====================
//  - 0阶: 同原版（黄油概率 25%）
//  - 1阶: 对某一个僵尸每攻击一次黄油概率 +5%，最高 50%（每僵尸独立累加）
//  - 2阶: 索敌僵尸越近攻速越快，4格→1格攻击间隔线性缩短至 1s
//  - 3阶: 每次投掷 0.5% 概率扔出大玉米炮（玉米加农炮弹，落地爆炸）
// ★ 黄油判定在攻击开始帧 hook（0x45F1E0，FindTargetAndFire 内）统一决定：
//   原生按判定设置 [plant+0x3C]=0x27（黄油动画）并据其创建子弹类型 →
//   动画显示与扔出子弹天然一致（修复原事件强制子弹 Type 与动画不同步的 BUG）。
//   僵尸身份用轮询帧缓存的本行最靠前僵尸；攻击计数用 POD pending 轮询帧落账。
static int g_cornButterBase = 25;              // 1阶黄油基础概率 (%)
static int g_cornButterUp = 5;                 // 1阶每攻击一次提升 (%)
static int g_cornButterMax = 50;               // 1阶概率上限 (%)
static int g_cornFastIntervalCs = 100;         // 2阶最近距(1格)攻击间隔（厘秒，1s）
static float g_cornCobProbability = 0.5f;      // 3阶大玉米炮触发概率 (%)
// 攻击计数落账（事件帧只写 POD pending，轮询帧写 map——防事件帧 map 插入崩溃铁律）
struct CornPultPending { DWORD plant; DWORD zombie; };
static CornPultPending g_cornPending[32];
static int g_cornPendingCount = 0;
// 每株玉米投手 → (僵尸 → 攻击次数)；onNewGame/onPlantRemove/onZombieRemove 清理防池复用
std::map<DWORD, std::map<DWORD, int>> g_cornPultHits;
// 缓存：玉米投手 → 本行最靠前(索敌目标)僵尸地址 / 距离(格)，-1/0=无或未缓存。
// ★ 事件帧只读此缓存（避免重操作），实际扫描在轮询帧 onGameObjectsUpdate 完成。
std::map<DWORD, DWORD> g_cornFrontZombie;
std::map<DWORD, float> g_cornFrontDist;

// —— 黄油判定核心（trampoline call，游戏原生线程执行）——
// 返回 1=黄油 / 0=玉米粒。只读 std::map（find 不插入），计数登记写 POD pending（轮询帧落账）。
static int __cdecl KernelpultButterDecide(DWORD plantAddr)
{
	if (!plantAddr || plantAddr < 0x10000)
		return 0;
	int exp = 0;
	auto expIt = g_plantExperience.find(plantAddr);
	if (expIt != g_plantExperience.end()) exp = expIt->second;
	int tier = GetPlantTier((int)SeedType::Kernelpult, exp);
	if (tier < 1)
	{
		// 0阶：同原版 25%
		return (rand() % 100 < 25) ? 1 : 0;
	}
	// 1阶+：按对该僵尸攻击次数累计概率（25% → +5%/次 → 上限 50%）
	DWORD frontZombie = 0;
	auto fzIt = g_cornFrontZombie.find(plantAddr);
	if (fzIt != g_cornFrontZombie.end()) frontZombie = fzIt->second;
	int prob = g_cornButterBase;
	if (frontZombie)
	{
		int hits = 0;
		auto pit = g_cornPultHits.find(plantAddr);
		if (pit != g_cornPultHits.end())
		{
			auto zit = pit->second.find(frontZombie);
			if (zit != pit->second.end()) hits = zit->second;
		}
		prob = g_cornButterBase + g_cornButterUp * hits;
		if (prob > g_cornButterMax) prob = g_cornButterMax;
		if (prob < 0) prob = 0;
		// 登记本次攻击（POD pending，轮询帧写 map 防池复用误判）
		if (g_cornPendingCount < 32)
		{
			g_cornPending[g_cornPendingCount].plant = plantAddr;
			g_cornPending[g_cornPendingCount].zombie = frontZombie;
			g_cornPendingCount++;
		}
	}
	return (rand() % 100 < prob) ? 1 : 0;
}

// 玉米投手黄油判定 hook @ 0x45F1E0（FindTargetAndFire 内玉米投手分支）
// 原代码 B8 04 00 00 00 = mov eax,4（随后 call RandRange; test eax,eax; jne 45F22D → 原生25%黄油）
//   trampoline：call KernelpultButterDecide(esi) 按自定义概率判定 →
//     黄油(eax=1, 反转后0) → jmp 45F1EE（原生黄油路径：状态0x3C=0x27 + 黄油子弹，动画/子弹天然一致）
//     玉米粒(eax=0, 反转后1) → jne 45F22D（原生玉米粒路径：CD=0x1E，动画/子弹保持玉米粒）
// 修复"篮子显示黄油但扔出玉米粒"的动画与子弹类型不同步 BUG。
static bool g_cornButterHookInstalled = false;
static void InstallKernelpultButterHook()
{
	if (g_cornButterHookInstalled) return;
	DWORD hookAddr = 0x45F1E0;
	BYTE raw[5];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 5);
	BYTE expect[5] = { 0xB8, 0x04, 0x00, 0x00, 0x00 };
	if (memcmp(raw, expect, 5) != 0)
		return;   // 字节不符（代码未解密/版本不同）→ 跳过不装防崩溃

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0) return;

	BYTE tp[64];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	// push esi（参数=植物地址）
	tp[p++] = 0x56;
	putRelCall((DWORD)&KernelpultButterDecide);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04; // add esp,4 清理参数
	tp[p++] = 0x83; tp[p++] = 0xF0; tp[p++] = 0x01; // xor eax,1（黄油1→0 / 玉米粒0→1）
	int jnePos = p;
	tp[p++] = 0x0F; tp[p++] = 0x85; put32(0);        // jne 45F22D（玉米粒 → 原生玉米粒路径）
	// 回填 jne 目标：偏移-偏移（rel32 = 目标 - 指令地址 - 6）
	*(int*)(tp + jnePos + 2) = (int)((DWORD)0x45F22D - ((DWORD)tramp + (DWORD)jnePos + 6));
	// 黄油 → jmp 45F1EE（原生黄油路径）
	putRelJmp(0x45F1EE);

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
}

// ==================== 剧毒体系（海蘑菇首发，后续毒系植物共用）====================
// 设计（2026-08-28 v3）：
//   - 剧毒标记存储：zombieAddr → 层数（std::map，与金盏花产出物/魅惑菇同模式）。
//     毒是永久状态（无时限），层数只增不减；毒系植物共用 AddPoisonStacks() 入口。
//   - 每秒 tick 造成"层数"点伤害，走 PVZ::Zombie::Hit（TakeDamage 正常流程）→ 优先伤害防具。
//   - 携带剧毒的僵尸变绿（reanim 基础色乘法染色，每帧重设）。
//   ★ v3 染色修复（2026-08-28 三轮排查结论）：
//     v1 SetColor 无效根因 = 游戏原生 0x52D3EA 是"栈取色"（mov eax,[esp+30]，
//     忽略 reanim 颜色）→ PVZClass 的 Animation::Lock/UnLock 机制：
//     UnLock(AP_ZOMBIECOLOR) 写 0x52D3EA = 0x909030EB（jmp 跳过栈取色）→ reanim 颜色生效。
//     修复 = 每帧调用 PVZ::Animation::UnLock(PVZ::AP_ZOMBIECOLOR)（每帧重写防 0x52xxxx
//     解密区重置），再 SetColor。
//     v2 的 0x52D2C8 绘制 hook 已证伪：诊断计数器 exec=0（该地址不在僵尸绘制路径，
//     mov edx,[0x722820] 属于其他函数），整套 trampoline 方案移除。
//   - 海蘑菇 5阶毒爆：命中时若层数≥阈值 → 15倍层数直伤 + 3×3范围僵尸附加 10 层；
//     **毒爆后目标层数清零**（用户规格：爆完重新叠毒）+ 同步 SetColor 白恢复原色。
//   - 安全：onZombieRemove 清理 + 轮询兜底（NotExist 即 erase），防僵尸内存池地址复用残留。
//   - 硬编码（用户明确不导出）：每秒伤害=层数、毒爆15倍、溅射10层、3×3列半径80px。
// 导出配置（plant_mechanics.ini）：
//   SEASHROOM_POISON_STACK_T0 / _T1 / _T3 = 0/1/3阶每发子弹附加层数
//   SEASHROOM_POISON_BURST_STACKS = 5阶毒爆触发阈值
static std::map<DWORD, int> g_poisonStacks;      // zombieAddr → 剧毒层数
static int g_poisonLastTickCs = 0;               // 上次毒 tick 时刻（Board.PlayingTime 厘秒）
static const int POISON_TICK_INTERVAL_CS = 100;  // tick 间隔：1 秒（100 厘秒）
static const int POISON_BURST_DMG_MULT = 15;     // 毒爆伤害 = 层数 × 15（硬编码）
static const int POISON_BURST_SPLASH_STACKS = 10; // 毒爆溅射附加层数（硬编码）
static const int POISON_BURST_RADIUS_PX = 80;    // 3×3 溅射：列方向半径 = 1 格宽（硬编码）
static int g_seaStackT0 = 1;                     // SEASHROOM_POISON_STACK_T0  0阶层数
static int g_seaStackT1 = 2;                     // SEASHROOM_POISON_STACK_T1  1阶层数
static int g_seaStackT3 = 3;                     // SEASHROOM_POISON_STACK_T3  3阶层数
static int g_seaBurstThreshold = 40;             // SEASHROOM_POISON_BURST_STACKS 毒爆阈值
static int g_poisonTintEnabled = 1;              // SEASHROOM_TINT_ENABLED 染色总开关（0=关闭染色/UnLock，仅保留毒伤，崩溃二分排查用）
// 毒爆粒子特效（复刻 S6 幽冥菇"大星星子弹命中爆出一堆幽冥小"观感）：
//   ★ S6 事实核查（用户纠正后确认）：S6 幽冥菇是 CE 汇编机制，S6 的 particles 目录与原版
//     逐字节一致（无自定义粒子定义/贴图），S6 寒冰菇攒层爆发亲证用 LOT_OF_SNOW(0x4D)
//     （S6中瞻全修复.CT 16750：mov eax,4D; call 453c80）——"一堆小光点四散渐隐"。
//     原版游戏文件里一切 STAR 相关（0x1D 等）都是杨桃的，与幽冥菇无关。
//   方案（用户拍板 + 数值表复核）：主特效 = 0x46（十进制 70，数值表"看星星特效"）染绿，
//     并用 OverrideImage(0x518600) 把粒子贴图整体替换为小喷菇孢子烟雾团：
//     PuffShroom_puff2.png（海蘑菇正统孢子，PuffSplat 定义同款）/ PuffShroom_puff1.png（大喷菇雾团）。
//     ★ 数值表编号是十六进制：46=0x46=70 十进制（PresentPickup，星形 STAR40 四溅）。
//       十进制 46(0x2E) 是路灯花照明 LanternShine——第一版踩过此坑，勿回退！
//     贴图指针从粒子定义表 [[0x6A9F0C]+effectId*8+4] → mEmitterDefs[0].mImage(+0x00) 纯读获取
//     （定义文件：PuffSplat→PUFF2、FumeCloud→PUFF1，均启动时随 main.pak 加载，零新增资源）。
//     0x46 三个发射器全部 imagecol/row/frames=0 单帧，换单帧 puff 图无越界风险。
//   OverrideImage 为逐实例覆盖（发射器实例 +0x54 槽），不影响游戏内其它同特效实例。
//   若观感需调：TINT_R/G/B 乘色；IMAGE1/2=0 关闭对应贴图替换；OFFSET_X/Y 位置微调。
static int g_seaBurstParticleEnabled = 1;        // SEASHROOM_BURST_PARTICLE_ENABLED 毒爆粒子总开关（0=关闭）
static int g_seaBurstEffect1 = 0x46;             // SEASHROOM_BURST_EFFECT1 主特效（0x46=70 数值表"看星星特效"，星形四溅）
static int g_seaBurstEffect2 = 0x46;             // SEASHROOM_BURST_EFFECT2 叠加特效（-1=关闭；同为 0x46 再叠一层）
static int g_seaBurstImage1 = 2;                 // SEASHROOM_BURST_IMAGE1 主特效贴图（0=不替换 1=PuffShroom_puff1 雾团 2=PuffShroom_puff2 孢子）
static int g_seaBurstImage2 = 1;                 // SEASHROOM_BURST_IMAGE2 叠加特效贴图（同上）
static int g_seaBurstOffsetX = 70;               // SEASHROOM_BURST_OFFSET_X 爆点水平偏移（+右/-左）
static int g_seaBurstOffsetY = 95;               // SEASHROOM_BURST_OFFSET_Y 爆点竖直偏移（+下/-上）
static int g_seaBurstTintR = 80;                 // SEASHROOM_BURST_TINT_R 孢子绿 R（乘色，255=不衰减该通道）
static int g_seaBurstTintG = 255;                // SEASHROOM_BURST_TINT_G 孢子绿 G
static int g_seaBurstTintB = 80;                 // SEASHROOM_BURST_TINT_B 孢子绿 B

// ==================== 墓碑吞噬者（GraveBuster, SeedType=11）等阶机制 ====================
// 设计（2026-10-21，3 阶即满阶）：
//   0阶：吞噬墓碑完成 → 原地"跳出"一个经验包（可拾取 → 拖到植物上 +经验）
//   1阶：每次吞噬成功 → 该植物卡剩余冷却减半
//   2阶：吞噬完成 → 原地等概率生成 普通/路障/铁桶/橄榄 僵尸
//   3阶：吞噬完成 → 再"跳出"一张随机植物卡片（本关卡槽随机，排除花盆/荷叶）；
//        用原版 Coin(PlantCard)（= 砸罐子同款）：弹出→落地→点击直接种植
//
// 经验来源（用户定案 2026-10-21）：
//   完全靠"分队友经验 + 肥料包/经验包"喂。★ 墓碑吞噬者消失时其经验**不分配给同行**，
//   而是写回"卡片级永久经验"（跨关卡存档 grave_buster_card.dat），下次种下自动继承。
//   ★ 模仿者墓碑吞噬者暂与普通卡合并计算（共用一份卡片经验，用户已确认可接受）。
//
// 触发（零 hook，项目铁律"能用每帧 tick 就别钩主循环"）：
//   每帧扫描 Board::GetAllGriditems<Grave>() 与上一帧比对；某格墓碑消失
//   且该格曾种过墓碑吞噬者（armed 表）⇒ 判定吞噬成功（此刻植物已被 Plant::Kill）。
//   依据：Plant::UpdateGraveBuster @0x45FC70（中文版反汇编实证）——
//     State==8 播 anim_eat 并置 +0x54=400；State==9 && +0x54==0 时
//     call 0x408E40 取本格墓碑 → call 0x44D000 移除墓碑 → 0x4679B0 Plant::Kill。
#define GB_MAX_ARMS    32      // 同时追踪的墓碑吞噬者上限
#define GB_MAX_ITEMS   16      // 同时存在的经验包掉落物上限
#define GB_MAX_GRAVES  96      // 每帧墓碑快照上限（原版单关墓碑远小于此）
#define GB_ARM_HOLD    150     // armed 记录在植物消失后的保留帧数（约 1.5 秒）

static int  g_gbCardExp          = 0;        // GB 卡片级永久经验（跨关卡）
static bool g_gbCardExpLoaded    = false;    // 是否已尝试从存档读取
static int  g_gbCardSavePending  = -1;       // >=0 = 待落盘的卡片经验
static int  g_gbExpPackGain      = 300;      // GB_EXP_PACK_GAIN 经验包给的经验
static float g_gbItemAnimSpeed   = 0.8f;     // GB_ITEM_ANIM_SPEED 经验包"跳出"动画速度倍率（1.0=原速）
static int  g_gbDigExp           = 0;        // GB_DIG_EXP 每次吞噬额外给"卡片"的经验（0=关闭，纯靠肥料/队友分经验）
static int  g_gbItemLifeCs       = 1800;     // GB_ITEM_LIFE_CS 经验包存在时长（厘秒）
static int  g_gbZombieTypes[8]   = {0, 2, 4, 7}; // GB_ZOMBIE_TYPES（ZombieType：0普通 2路障 4铁桶 7橄榄）
static int  g_gbZombieTypeCount  = 4;
static int  g_gbExcludeSeeds[8]  = {16, 33};  // GB_CARD_EXCLUDE 随机卡片排除（16睡莲 33花盆）
static int  g_gbExcludeCount     = 2;
static int  g_gbDebug            = 0;        // GB_DEBUG 1=写 D:\pvz_gb_debug.txt

struct GbArmRec { int plant; int row; int col; int tier; int hold; };
static GbArmRec g_gbArms[GB_MAX_ARMS];
static int      g_gbArmCount = 0;

struct GbGraveKey { int row; int col; };
static GbGraveKey g_gbPrevGraves[GB_MAX_GRAVES];
static int        g_gbPrevGraveCount = 0;

// 经验包掉落物（自绘 + 自写"跳出"抛物线；不锚定植物——产出时植物已死）
struct GbItemRec
{
	float x, y;         // 屏幕坐标（中心）
	float vy;           // 竖直速度（px/帧）
	int   groundY;      // 落地 Y
	int   spawnCs;      // 出生时刻（Board.PlayingTime 厘秒）
	int   bounces;      // 已反弹次数
	int   settled;      // 1=已静止
	int   alive;        // 1=有效
};
static GbItemRec g_gbItems[GB_MAX_ITEMS];
static int g_gbItemCount = 0;
static int g_gbSelected  = -1;   // 被拾起的经验包下标（-1=无）

static void GbFrame(DWORD boardAddress);          // 每帧轮询（实现体在文件末尾）
static void GbResetAll();                          // 新关卡重置
static void DrawGbUI();                            // onDrawUITop 绘制
static int  GbHandleMouseDown(DWORD boardAddr, int x, int y);  // Board::MouseDown 交互

// ==================== 机枪射手配置（GATLING_*，实现体在文件后段）====================
// 变量必须定义在此处之前（LoadPlantMechanicsConfig 在下方需要读写它们）
static int   g_gatlingUltExpCost   = 10000;  // GATLING_ULT_EXP_COST        每满该值溢出经验 → 消耗并开一次大招
static int   g_gatlingUltCount     = 180;    // GATLING_ULT_COUNT           单次大招发射总数（颗）
static int   g_gatlingUltDuration  = 200;    // GATLING_ULT_DURATION_TICKS  单次大招持续（tick；v9: 逻辑帧率实测≈100 tick/s，200≈2秒）
static float g_gatlingUltSpeed     = 3.33f;  // GATLING_ULT_SPEED           大招弹速率（px/tick，原版豌豆同款）
static float g_gatlingUltSpreadDeg = 15.0f;  // GATLING_ULT_SPREAD_DEG      锥形半角（度）
static int   g_gatlingUltYRand     = 20;     // GATLING_ULT_Y_RAND          出生 Y 随机偏移幅度（px）

// ==================== 究极大喷菇配置（ULF_*，实现体在文件后段）====================
// 变量必须定义在此处之前（LoadPlantMechanicsConfig 在下方需要读写它们）
static int  g_ulfEnabled        = 1;    // ULF_ENABLED        总开关（0=恢复原版大喷菇，A/B 排查用）
static int  g_ulfIntervalCs     = 50;   // ULF_INTERVAL_CS    攻击间隔（厘秒，50=0.5 秒）
static int  g_ulfDamage         = 100;  // ULF_DAMAGE         每次攻击伤害
static int  g_ulfSlowCs         = 200;  // ULF_SLOW_CS        减速时长（厘秒）
static int  g_ulfFreezeGain     = 10;   // ULF_FREEZE_GAIN    每次攻击累计的冻结值
static int  g_ulfFreezeCapBase  = 100;  // ULF_FREEZE_CAP_BASE 冻结值初始上限
static int  g_ulfFreezeCapStep  = 100;  // ULF_FREEZE_CAP_STEP 每次冻结后上限增量
static int  g_ulfFreezeCapMax   = 400;  // ULF_FREEZE_CAP_MAX  上限最大值
static int  g_ulfFreezeCs       = 400;  // ULF_FREEZE_CS      冻结时长（厘秒，寒冰菇=4 秒）
static int  g_ulfCharmPercent   = 1;    // ULF_CHARM_PERCENT  魅惑概率（%）
static int  g_ulfCharmHpPercent = 50;   // ULF_CHARM_HP_PERCENT 生命值低于该百分比才可能魅惑
static int  g_ulfCharmTotalHp   = 1;    // ULF_CHARM_TOTAL_HP 1=按总体生命(护甲+本体) 0=仅本体
static int  g_ulfBoomDamage     = 360;  // ULF_BOOM_DAMAGE    魅惑成功后 3×3 爆炸伤害
static int  g_ulfBoomRowRange   = 1;    // ULF_BOOM_ROW_RANGE 3×3 的行半径（±N 行）
static int  g_ulfBoomXRange     = 120;  // ULF_BOOM_X_RANGE   3×3 的 X 半径（px，120=3 格宽的一半）
static int  g_ulfBoomSound      = 0;    // ULF_BOOM_SOUND     爆炸音效 ID（0=不播）
static int  g_ulfFrontOnly      = 0;    // ULF_FRONT_ONLY     1=只打植物右侧（X>=植物X）
static int  g_ulfDebug          = 1;    // ULF_DEBUG          1=每秒往 D:\pvz_ulf_debug.txt 写一行自检（排障用）
static void UltFumeResetAll();          // 新游戏重置（实现体在文件后段）
static void UlfDebugFlush(const char* tag); // 自检日志（实现体在文件后段）
static void FumeResetAll();             // 大喷菇等阶：新游戏重置（实现体在文件后段）
static void UpdateFumeTierFrame(DWORD boardAddress);   // 大喷菇等阶：每帧轮询（实现体在文件后段）

// ==================== 寒冰菇（IceShroom, SeedType=14）等阶机制 ====================
//   0阶 同原版（冻结全屏僵尸 4 秒）；1/2/3阶 满阶（T4<=T3 配置特征，同樱桃）。
//   1阶：冻结瞬间造成 80 点伤害（不导出，代码常量 ICE_T1_DAMAGE）。
//   2阶：冻结时长延长为 8 秒（ICESHROOM_FREEZE_CS，厘秒）。
//   3阶：冻结后以寒冰菇为中心留下 3×3 冰法阵（持续 ICESHROOM_FIELD_DURATION），
//       走进的僵尸减速 + 受到所有伤害 +ICESHROOM_VULNERABLE_PERCENT% 结算。
//   冰法阵用路灯花灯光特效（数值表"2E 光：辉耀1"LanternShine）整体染蓝标注，
//   中心=寒冰菇所在格中心；灯光持续发光，生成时一次性 spawn。
//
// ★ 设计（防崩溃铁律）：寒冰菇爆炸时的冻结/伤害/法阵生成都在轮询帧延迟执行。
//   onPlantRemove 只登记 POD 请求（g_iceBoomReqs），不动游戏对象、不调游戏函数；
//   IceFieldFrame（轮询帧）才遍历僵尸做 Froze/HitBody/Decelerate/创建粒子特效。
//   冻结时长用"再断言"窗口（g_iceGrace）覆盖原版晚到的 400cs 冻结，保证 8 秒生效。
static int  g_iceFreezeCs    = 800;    // ICESHROOM_FREEZE_CS     2/3阶冻结时长（厘秒，800=8秒）
static int  g_iceVulnPercent = 20;     // ICESHROOM_VULNERABLE_PERCENT 3阶脆弱增伤（%）
static int  g_iceFieldCs     = 2000;   // ICESHROOM_FIELD_DURATION   3阶冰法阵持续（厘秒，2000=20秒）
static const int ICE_FREEZE_DEFAULT_CS = 400;  // 原版寒冰菇冻结时长（0/1阶）4 秒
static const int ICE_T1_DAMAGE         = 80;   // 1阶冻结瞬间伤害（不导出）
static const int ICE_FIELD_EFFECT      = 0x2E; // 数值表"2E 光：辉耀1"（路灯花 LanternShine 灯光）
// 路灯花光效默认黄白光，乘色染成蓝（255=该通道不衰减）：
static const int ICE_FIELD_R = 120;   // 浅蓝：R调高 → 偏亮
static const int ICE_FIELD_G = 180;   // G调高 → 浅蓝更亮
static const int ICE_FIELD_B = 255;   // B拉满 → 蓝色
static const int ICE_GRACE_POLLS       = 90;   // 冻结时长再断言窗口（帧数，覆盖晚到的原版冻结）
// 爆炸登记队列（事件帧只写 POD，轮询帧消费 —— 与其它延迟执行机制一致）
struct IceBoomReq { int row, col, tier; };
static IceBoomReq g_iceBoomReqs[16];
static int g_iceBoomReqCount = 0;
// 冻结时长再断言记录（爆炸后短期内每帧强制刷新冻结，碾压原版可能晚到的 400cs）
struct IceGraceRec { int tier; int remainPoll; };
static IceGraceRec g_iceGrace[16];
static int g_iceGraceCount = 0;
// 活动冰法阵（中心像素 + 计时 + 持有的光圈粒子句柄）
// ★计时：不用 GetTickCount（暂停时仍走）。用"未暂停时累加运行时长"：
//   lastReal 每帧记录，仅当未暂停时把 (now-lastReal) 累进 accumMs；暂停时 lastReal
//   照常前移但不累加 → 暂停期间法阵不倒计时。恢复后首帧增量≈正常帧长。
// psys[]: 叠放的路灯光特效句柄（法阵到期时逐一 Die 手动移除，避免光圈残留）
// psysId[]: 创建时读到的粒子系统 Id（槽位 +0x9C）；Die 前必须比对——
//   粒子槽是游戏池化复用的，若槽已被回收复用（Id 变了）绝不能 Die（会写坏别人的结构）
struct IceFieldRec { float cx, cy; int row; DWORD accumMs, lastReal; DWORD psys[2]; DWORD psysId[2]; int psysCount; };
static IceFieldRec g_iceFields[16];
static int g_iceFieldCount = 0;
// 在法阵内（受脆弱增伤）的僵尸地址集合；轮询帧每帧重建，onZombieRemove 兜底清理
static std::set<DWORD> g_iceVulnZombies;
static int g_iceFxErr = 0;   // 粒子/异常留痕计数（排障用）
// 淡蓝高不透明光晕贴图（particles\LanternShine_ice.png，复制改色自 LanternShine.png）
static DWORD g_iceFieldImage = 0;
static bool g_iceFieldImageLoaded = false;
// ★贴图位置偏移：光晕贴图中心相对"格子中心"的偏移（实测格子中心偏左上，需要右移/下移）
//   实测基准 +50/+54 → 再左移16、上移9 定稿：+34/+45
static const float ICE_FIELD_DX = 34.0f;
static const float ICE_FIELD_DY = 45.0f;

// ==================== 毁灭菇（Doomshroom, SeedType=15）等阶机制 ====================
//   0阶 同原版；1阶 爆炸半径扩到 350px；2阶 全屏；3阶(+) 全屏 + 原地 3×3 毁灭领域。
//   ★化灰死亡 = 原版灰烬路径 ApplyBurn(0x532B70)：反汇编 0x41D8A0 化灰分支证明原版
//   灰烬爆炸对每只僵尸是"二选一"——化灰参数非 0 时只调 ApplyBurn（不走 TakeDamage），
//   ApplyBurn 内部守卫：NotExist/死亡中(State==2)/免疫类型跳过；本体 HP>=1800 只烧
//   1800 伤害（大块头不死，同原版樱桃/毁灭）。pvzclass 封装 = z.Blast()。
//   ★毁灭领域：领域内僵尸受到的伤害无视一类/二类防具，直接结算本体（TakeBodyDamage）；
//   防爆门僵尸的限伤代码优先级更高，领域穿甲对它无效。
//   领域持续 ICESHROOM_FIELD_DURATION（与寒冰菇冰法阵共用 g_iceFieldCs），
//   视觉暂用寒冰菇冰法阵特效（路灯光晕 + 淡蓝贴图），后续换新外观。
//   防崩溃铁律同寒冰菇：事件帧只登记 POD 请求，轮询帧才调游戏函数。
struct DoomBoomReq { int row, col, tier; };
static DoomBoomReq g_doomBoomReqs[8];
static int g_doomBoomReqCount = 0;
// 活动毁灭领域（结构/计时/槽位复用防护与冰法阵完全一致）
struct DoomFieldRec
{
	float cx, cy;
	int row;                       // 领域中心行（3×3 判定用 Row 字段精确判定，2026-09-13）
	DWORD accumMs, lastReal;
	DWORD emberAccum, dustAccum;   // 余烬/尘烟撒播计时（暂停感知同 accumMs）
	DWORD fogAccum;                // 毒雾生成计时（贴图层方案后不再累加，保留字段兼容）
	DWORD fogImgCur;               // 雾层当前档位贴图指针（0=未换过；避免每帧重复 OverrideImage）
	DWORD psys[2]; DWORD psysId[2]; int psysCount;
	int gen;                       // 全局唯一代号（槽位尾删交换也不串）
};
static DoomFieldRec g_doomFields[8];
static int g_doomFieldCount = 0;
static int g_doomFieldGen = 0;     // 领域代号计数器（跨槽位唯一）
// 领域内僵尸地址集合（轮询帧每帧重建 → 僵尸离开/领域到期自动失效，无需清理钩子）
static std::set<DWORD> g_doomDomainZombies;
static const int DOOM_T1_RADIUS = 350;   // 1阶爆炸半径（px）
static int g_doomFxErr = 0;              // 轮询帧异常留痕计数（排障用）
// 领域余烬/尘烟粒子特效 ID（可在 plant_mechanics.ini 调换试效果；<=0 = 关闭该层）
// 可选值参考（数值表十六进制即本 ID）：76=0x4C FireballDeath（Zomboss 火球落地爆开：地面火+尘土）
//   75=0x4B Zombie_boss_fireball（含球体本体，不只地面火）；79=0x4F Fireball_Trail（小，用户已否）
//   98=0x62 Dust_Foot（走路扬尘）；97=0x61 Dust_Squash（大尘爆）；60=0x3C GloomCloud（大喷菇紫烟）
// ★ 余烬/尘烟已固化关闭（2026-09-13 起 ini 不再外置；-1 = 关闭该层，负值即禁用）
static int g_doomEmberEffect = -1;       // 原 DOOM_FIELD_EMBER_EFFECT（76=0x4C FireballDeath）
static int g_doomDustEffect  = -1;       // 原 DOOM_FIELD_DUST_EFFECT（98=0x62 Dust_Foot）
static const int DOOM_EMBER_INTERVAL_MS = 600;   // 每个领域撒火星间隔
static const int DOOM_DUST_INTERVAL_MS  = 400;   // 每个领域撒尘烟间隔
static const float DOOM_SPRINKLE_X = 90.0f;      // 撒播点 X 半幅（略盖 ±80 判定边缘）
static const float DOOM_SPRINKLE_Y = 95.0f;      // 撒播点 Y 半幅

// ---- 紫色毒雾覆盖（2026-09-12 晚：放弃粒子轨道方案，改冰法阵同款"常驻贴图层"）----
// 半透明紫黑雾贴图直接铺满 3x3 区域（原版迷雾质感，纹理/染色/羽化全烘进 PNG）：
// 领域创建时 SeaBurstSpawnParticle(0x68 Credits_fog 槽静态变体) + OverrideImage 换雾贴图，
// 到期校验槽位 Id 后 IceParticleDie（与冰法阵完全一致的防护）。Credits_fog 覆写已撤销。
// 贴图由 make_doomfog_area.py 生成（384x384，2 档 alpha：a22 淡入淡出 / a80 常驻）。
static int g_doomFogEnabled = 1;         // DOOM_FIELD_FOG（<=0 关闭雾层）
static const int DOOM_FOG_FADE_MS = 600; // 淡入/淡出时长（期间用 a22 档贴图）
static DWORD g_doomFogImgA80 = 0;        // 常驻档雾贴图
static DWORD g_doomFogImgA22 = 0;        // 淡档雾贴图
static const float DOOM_FOG_AREA_HW = 192.0f;  // 贴图半宽/半高（384x384 中心对齐领域中心）
static const float DOOM_FOG_AREA_HH = 192.0f;

// ---- 领域内受伤"紫色灼烧"火焰（2026-09-12）----
// 需求：毁灭领域范围内僵尸受到伤害时，播放火豆命中火焰动画（reanim type 0x22，原版复刻
// 见 FireBallHitEffect），颜色改为紫色。分摊铁律：TakeDamage hook 内只登记 POD 请求
//（事件帧禁 CRT / 禁容器插入 / 禁重活），轮询帧统一直调 0x453C30 创建 + 覆盖色染紫。
static const int DOOM_BURN_REQ_MAX = 32;
static DWORD g_doomBurnReqZ[DOOM_BURN_REQ_MAX];
static float g_doomBurnReqX[DOOM_BURN_REQ_MAX];
static float g_doomBurnReqY[DOOM_BURN_REQ_MAX];
static float g_doomBurnReqZ34[DOOM_BURN_REQ_MAX];   // 诊断用：僵尸 +0x34
static int   g_doomBurnReqRow[DOOM_BURN_REQ_MAX];   // 诊断用：僵尸 Row(+0x1C)
static DWORD g_doomBurnReqLayer[DOOM_BURN_REQ_MAX];
static volatile LONG g_doomBurnReqCount = 0;
static int g_doomBurnEnabled = 1;              // <=0 关闭紫焰（调试开关）

// hook 内调用（TakeDamage 路径）：只做可读校验 + POD 写，无 CRT/无分配/无重活。
// ★ 坐标用直接指针读（铁律：MemSafeRead 在 hook 中可能崩溃，改用纯指针/__asm）
static void DoomBurnRegister(DWORD zombieAddr)
{
	if (!g_doomBurnEnabled) return;
	if (!zombieAddr || !CrashIsReadable(zombieAddr, 0x40)) return;
	int n = g_doomBurnReqCount;
	if (n < 0 || n >= DOOM_BURN_REQ_MAX) return;
	g_doomBurnReqZ[n] = zombieAddr;
	g_doomBurnReqX[n] = *(volatile float*)(zombieAddr + 0x2C);
	g_doomBurnReqY[n] = *(volatile float*)(zombieAddr + 0x30);
	g_doomBurnReqZ34[n] = *(volatile float*)(zombieAddr + 0x34);
	g_doomBurnReqRow[n] = *(volatile int*)(zombieAddr + 0x1C);
	g_doomBurnReqLayer[n] = *(volatile DWORD*)(zombieAddr + 0x20) + 1;
	g_doomBurnReqCount = n + 1;
}

// 轮询帧创建紫焰：直调 0x453C30（DEP 铁律禁用 Memory::Execute；坐标管道照抄 FireBallHitEffect，
// 输入换成僵尸 X/Y：X=[z+0x2C]-qword[0x679338]、Y=[z+0x30]+qword[0x67A288]）
static DWORD g_doomBurnFxApp = 0;
static DWORD g_doomBurnFxLayer = 0;
static DWORD g_doomBurnFxX = 0;    // float 位模式（跨 __asm 铁律：float 局部不可靠）
static DWORD g_doomBurnFxY = 0;
static DWORD g_doomBurnFxCalled = 0;   // 调用计数（asm 内 inc，诊断用）
static DWORD g_doomBurnFxCreated = 0;  // 成功创建计数（asm 内 inc，诊断用）
static float g_doomBurnFixX = 38.0f;   // 火焰锚点 X 修正（与火豆命中管道同值 +38）
static float g_doomBurnFixY = 35.0f;   // 火焰锚点 Y 修正（火豆管道为 -20；用户实测再下移 55 → +35）

static void DoomPurpleBurnFx(DWORD lawnApp, float x, float y, DWORD layer)
{
	if (!lawnApp) return;
	g_doomBurnFxApp = lawnApp;
	g_doomBurnFxLayer = layer;
	g_doomBurnFxX = *(DWORD*)&x;
	g_doomBurnFxY = *(DWORD*)&y;
	__try
	{
	__asm
	{
		pushad
		inc dword ptr [g_doomBurnFxCalled]
		mov eax, g_doomBurnFxApp
		mov ebx, 0x22                    // reanim 0x22 = 火豆命中火焰（原版 0x46E25F 段）
		mov ecx, g_doomBurnFxLayer
		push ecx
		sub esp, 8
		; ★ 槽位修正（2026-09-13，用户实测"偏差随行高 100 递增"= X/Y 互换特征）：
		;   引擎真实参数顺序 [esp]=X、[esp+4]=Y；FireBallHitEffect 注释把 X/Y 标反，
		;   但它的字段映射（slot4←Y 源、slot0←X 源）才是对的：
		;   子弹 X@+0x30 / Y@+0x34（pvzclass 与社区一致）→ slot0←0x30(X)、slot4←0x34(Y) ✓
		;   僵尸 X@+0x2C / Y@+0x30 → 同理 slot0←0x2C(X)、slot4←0x30(Y)。
		mov edx, offset g_doomBurnFxY
		fld dword ptr [edx]
		mov edx, offset g_doomBurnFixY
		fadd dword ptr [edx]             ; Y + 35.0（火豆原 -20，用户要求再下移 55）
		fstp dword ptr [esp + 4]
		mov edx, offset g_doomBurnFxX
		fld dword ptr [edx]
		mov edx, offset g_doomBurnFixX
		fadd dword ptr [edx]             ; X + 38.0（火豆管道同值）
		fstp dword ptr [esp]
		mov edx, 0x453C30
		call edx                         // eax = Animation*（stdcall ret 0xC 清 3 参数）
		test eax, eax
		je dpb_done                      // 创建失败直接退（防空指针写崩）
		mov edi, eax
		inc dword ptr [g_doomBurnFxCreated]
		// 原版字段初始化（0x46E298-0x46E2B9）
		mov edx, 0x67952C
		fld dword ptr [edx]
		fstp dword ptr [edi + 4]
		mov edx, 0x679638
		fld dword ptr [edx]
		fstp dword ptr [edi + 8]
		mov edx, 0x679928
		fld dword ptr [edx]
		fstp dword ptr [edi + 0x24]
		mov edx, 0x664A5C
		fld dword ptr [edx]
		fstp dword ptr [edi + 0x34]
		; 染色改走项目已验证通道（覆盖色 +0x80 从未验证成功：用户实测"颜色未变化"）：
		;   乘色 +0x48..0x54（海蘑菇毒色同款）：压掉橙色的绿分量
		;   加算 +0x6C..0x78（僵尸闪白同款）：补蓝紫 → 橙焰变紫
		mov dword ptr [edi + 0x48], 200
		mov dword ptr [edi + 0x4C], 100
		mov dword ptr [edi + 0x50], 255
		mov dword ptr [edi + 0x54], 255
		mov dword ptr [edi + 0x6C], 0
		mov dword ptr [edi + 0x70], 0
		mov dword ptr [edi + 0x74], 160
		mov dword ptr [edi + 0x78], 255
	dpb_done:
		popad
	}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_doomFxErr++;
	}
}

static void IceLog(const char* fmt, ...);   // 前向声明（实体在下方寒冰菇调试区，毁灭菇日志复用）

// 首次创建领域时一次性加载雾贴图（同 LoadIceFieldImage 模式；缺失自动重试）
// ★ 2026-09-12 修复：旧守卫查 g_doomFogImgLoaded，被调用方进门前已置 true → 短路 return，
//   GetSharedImage 从未执行 → fogImg 恒 0x0（特效不显示的真凶，与贴图/路径无关）。
//   现改为查图片指针本身（与 LoadIceFieldImage 检查 g_iceFieldImage 同模式）。
static void LoadDoomFogAreaImages()
{
	__try
	{
		if (g_doomFogImgA80 && g_doomFogImgA22) return;   // 幂等：两张齐才跳过；缺图每次领域创建都重试
		DWORD isNew = 0;
		Draw::PString variant = Draw::ToString("");
		Draw::PString p80 = Draw::ToString("images\\DoomFog_Area_a80.png");
		DWORD s80 = Draw::GetSharedImage(isNew, variant, p80);
		if (s80) g_doomFogImgA80 = Draw::SharedImageRefToImage(s80);
		Draw::PString p22 = Draw::ToString("images\\DoomFog_Area_a22.png");
		DWORD s22 = Draw::GetSharedImage(isNew, variant, p22);
		if (s22) g_doomFogImgA22 = Draw::SharedImageRefToImage(s22);
		IceLog("doom fog load: s80=0x%X s22=0x%X a80=0x%X a22=0x%X",
			s80, s22, g_doomFogImgA80, g_doomFogImgA22);   // 失败留痕（轮询帧 fopen 安全）
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 首帧一次性加载冰法阵光晕贴图（同 LoadIceFireImages 模式；缺失时自动重试）
static void LoadIceFieldImage()
{
	__try
	{
		if (g_iceFieldImage) return;
		DWORD isNew = 0;
		Draw::PString variant = Draw::ToString("");
		Draw::PString path = Draw::ToString("particles\\LanternShine_ice.png");
		DWORD shared = Draw::GetSharedImage(isNew, variant, path);
		if (shared)
			g_iceFieldImage = Draw::SharedImageRefToImage(shared);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ---- 寒冰菇调试日志（仅轮询帧调用，fopen 安全；崩溃排查铁律：留痕优于空实现）----
static void IceLog(const char* fmt, ...)
{
	FILE* f = fopen("D:\\pvz_ice_debug.txt", "a");
	if (!f) return;
	SYSTEMTIME st;
	GetLocalTime(&st);
	fprintf(f, "[%02d:%02d:%02d.%03d] ", st.wHour, st.wMinute, st.wSecond, st.wMilliseconds);
	va_list ap;
	va_start(ap, fmt);
	vfprintf(f, fmt, ap);
	va_end(ap);
	fprintf(f, "\r\n");
	fclose(f);
}

// 加载特殊机制配置
// 解析逗号分隔整数列表（"0,2,4,7"）→ out，返回解析到的个数
// 用于 GB_ZOMBIE_TYPES / GB_CARD_EXCLUDE 这类不定长列表
static int ParseIntList(const std::string& s, int* out, int maxN)
{
	int n = 0;
	size_t pos = 0;
	while (pos <= s.size() && n < maxN)
	{
		size_t comma = s.find(',', pos);
		std::string tok = (comma == std::string::npos) ? s.substr(pos) : s.substr(pos, comma - pos);
		size_t b = tok.find_first_not_of(" \t");
		size_t e = tok.find_last_not_of(" \t");
		if (b != std::string::npos)
			out[n++] = SafeAtoi(tok.substr(b, e - b + 1).c_str());
		if (comma == std::string::npos)
			break;
		pos = comma + 1;
	}
	return n;
}

void LoadPlantMechanicsConfig()
{
	g_poisonTintEnabled = 1;
	g_knockbackProbability = 20;
	g_knockbackDistance = 40;
	g_doubleShotProbability = 30;
	g_repeaterIcePeaProbability = 20;
	g_repeaterFirePeaProbability = 20;
	g_repeaterIceFirePeaProbability = 20;
	// 玉米投手机制默认值
	g_cornButterBase = 25;
	g_cornButterUp = 5;
	g_cornButterMax = 50;
	g_cornFastIntervalCs = 100;
	g_cornCobProbability = 0.5f;
	// 大嘴花机制默认值
	g_chomberBitePercent = 10;
	// 高坚果机制默认值
	g_tallnutT1MaxHp = 8000;
	g_tallnutAntiKillDmg = 1000;
	// 大蒜机制默认值
	g_garlicT1MaxHp = 600;
	g_garlicArrowOffX = 34;
	g_garlicArrowOffY = 52;
	g_garlicDebug = 0;
	g_garlicEnabled = 1;
	g_garlicRowHookState = 0;
	g_garlicRowHookTries = 0;
	g_garlicSmashHookState = 0;
	g_garlicSmashHookTries = 0;
	// 西瓜投手机制默认值
	g_melonChainProbability = 42.0f;
	g_melonCannonDamage = 220;
	// 冰西瓜机制默认值
	g_iceMelonFreezeProbability = 20;
	g_iceMelonVolleyCount = 14;
	// 西瓜选择窗口布局：定稿值已在 MEL_* 静态常量初始化处，此处不再覆盖
	//（曾在此重置旧默认值 140/640/130 导致布局回退——已删）
	// 寒冰菇机制默认值
	g_iceFreezeCs    = 800;   // ICESHROOM_FREEZE_CS  2/3阶冻结时长（厘秒）
	g_iceVulnPercent = 20;    // ICESHROOM_VULNERABLE_PERCENT 3阶脆弱增伤（%）
	g_iceFieldCs     = 2000;  // ICESHROOM_FIELD_DURATION 3阶冰法阵持续（厘秒）
	// 毁灭菇领域默认值（外观已固化：余烬/尘烟关闭 -1；ini 项已于 2026-09-13 移除）
	g_doomEmberEffect = -1;   // 原 DOOM_FIELD_EMBER_EFFECT（76=0x4C FireballDeath）
	g_doomDustEffect  = -1;   // 原 DOOM_FIELD_DUST_EFFECT（98=0x62 Dust_Foot）
	g_doomFogEnabled = 1;     // 原 DOOM_FIELD_FOG（紫雾贴图层开关；0=关闭）
	// 磁力菇机制默认值
	g_magShieldHp    = 300;   // MAGNET_SHIELD_HP     护盾耐久
	g_magRadiusBonus = 90;    // MAGNET_RADIUS_BONUS  2阶吸铁半径加成(px)
	g_magThrowDamage = 300;   // MAGNET_THROW_DAMAGE  3阶扔铁器伤害
	g_magThrowMs     = 350;   // MAGNET_THROW_MS      飞行总时长(ms，上限 350)
	g_magLadderHp    = 500;   // MAGNET_LADDER_HP     地上梯子耐久(原版 500)
	// 护盾/闪光贴图偏移已定稿 → 硬编码常量 MAG_SHIELD_OFF_* / MAG_SHIELD_FX_OFF_*，不再走 ini

	// 墓碑吞噬者机制默认值
	g_gbExpPackGain     = 300;               // GB_EXP_PACK_GAIN
	g_gbItemAnimSpeed   = 0.8f;              // GB_ITEM_ANIM_SPEED（用户实测"跳出有点快"→ 0.8 倍速）
	g_gbDigExp          = 0;                 // GB_DIG_EXP（0=纯靠肥料/队友分经验，按用户定案）
	g_gbItemLifeCs      = 1800;              // GB_ITEM_LIFE_CS
	g_gbZombieTypes[0] = 0;                  // 普通
	g_gbZombieTypes[1] = 2;                  // 路障
	g_gbZombieTypes[2] = 4;                  // 铁桶
	g_gbZombieTypes[3] = 7;                  // 橄榄
	g_gbZombieTypeCount = 4;
	g_gbExcludeSeeds[0] = 16;                // 睡莲
	g_gbExcludeSeeds[1] = 33;                // 花盆
	g_gbExcludeCount    = 2;
	g_gbDebug           = 0;

	std::ifstream file("plant_mechanics.ini");
	if (!file.is_open())
		return;

	std::string line;
	while (std::getline(file, line))
	{
		if (line.empty() || line[0] == ';' || line[0] == '#')
			continue;

		size_t eqPos = line.find('=');
		if (eqPos == std::string::npos)
			continue;

		std::string key = line.substr(0, eqPos);
		std::string value = line.substr(eqPos + 1);

		size_t kStart = key.find_first_not_of(" \t");
		size_t kEnd = key.find_last_not_of(" \t");
		if (kStart == std::string::npos)
			continue;
		key = key.substr(kStart, kEnd - kStart + 1);

		size_t vStart = value.find_first_not_of(" \t");
		if (vStart == std::string::npos)
			continue;
		std::string vstr = value.substr(vStart);

		// 浮点配置（玉米投手：间隔/概率可为小数）
		if (key == "CORNPULT_FAST_INTERVAL")
		{
			g_cornFastIntervalCs = (int)((float)std::atof(vstr.c_str()) * 100.0f + 0.5f);
			if (g_cornFastIntervalCs < 50) g_cornFastIntervalCs = 50;   // 下限 0.5s 防过速
			continue;
		}
		else if (key == "CORNPULT_COB_PROBABILITY")
		{
			g_cornCobProbability = (float)std::atof(vstr.c_str());
			if (g_cornCobProbability < 0.0f) g_cornCobProbability = 0.0f;
			continue;
		}
		else if (key == "MELON_CHAIN_PROBABILITY")
		{
			// 西瓜投手连投概率（%，可小数）
			g_melonChainProbability = (float)std::atof(vstr.c_str());
			if (g_melonChainProbability < 0.0f) g_melonChainProbability = 0.0f;
			if (g_melonChainProbability > 100.0f) g_melonChainProbability = 100.0f;
			continue;
		}

		int val = SafeAtoiLog(vstr.c_str(), key.c_str());

		if (key == "KNOCKBACK_PROBABILITY")
			g_knockbackProbability = val;
		else if (key == "KNOCKBACK_DISTANCE")
			g_knockbackDistance = val;
		else if (key == "DOUBLE_SHOT_PROBABILITY")
			g_doubleShotProbability = val;
		else if (key == "SUNFLOWER_AURA_SPEED_BOOST")
			g_sunflowerAuraBoost = val / 100.0f;
		else if (key == "SNOWPEA_FREEZE_PROBABILITY")
			g_snowPeaFreezeProbability = val;
		else if (key == "SNOWPEA_ICICLE_PROBABILITY")
			g_snowPeaIcicleProbability = val;
		else if (key == "PEASHOOTER_T5_SKIN")
			g_pst5SkinEnabled = (val != 0) ? 1 : 0;
		else if (key == "SUNFLOWER_3_SKIN")
			g_sunf3SkinEnabled = (val != 0) ? 1 : 0;
		else if (key == "REPEATER_ICE_PEA_PROBABILITY")
			g_repeaterIcePeaProbability = val;
		else if (key == "REPEATER_FIRE_PEA_PROBABILITY")
			g_repeaterFirePeaProbability = val;
		else if (key == "REPEATER_ICE_FIRE_PEA_PROBABILITY")
			g_repeaterIceFirePeaProbability = val;
		else if (key == "SCAREDY_SPEED_DOWN")
			g_scaredySpeedDownMs = val;
		else if (key == "SCAREDY_SPEED_UP")
			g_scaredySpeedUpMs = val;
		else if (key == "BLOVER_KNOCKBACK_DISTANCE")
			g_bloverKnockbackDistance = val;
		else if (key == "BLOVER_SPEED_BOOST_REDUCTION")
			g_bloverSpeedBoostReduction = val / 100.0f;
		else if (key == "BLOVER_SPEED_BOOST_DURATION")
			g_bloverSpeedBoostDuration = val;
		else if (key == "EXP_POUCH_SUN_COST")
			g_expPouchSunCost = val;
		else if (key == "EXP_POUCH_EXP_GAIN")
			g_expPouchExpGain = val;
		else if (key == "EXP_POUCH_COOLDOWN")
			g_expPouchCooldownCs = val;
		else if (key == "HEAPWATCH")
			g_heapWatchOn = (val != 0) ? 1 : 0;   // 堆完整性看门狗（1=开，0=关）
		else if (key == "MG_WATER_HEAL")
			g_mgWaterHeal = val;
		else if (key == "MG_BOOST_PERCENT")
			g_mgBoostPercent = val;
		else if (key == "MG_BOOST_DURATION")
			g_mgBoostDurationCs = val;
		else if (key == "MG_SPRAY_DPS")
			g_mgSprayDps = val;
		else if (key == "MG_SPRAY_DURATION")
			g_mgSprayDurationCs = val;
		else if (key == "MG_ITEM_MAX")
			g_mgItemMax = val;
		else if (key == "MG_PRODUCE_INTERVAL_CS")
			g_mgProduceIntervalCs = val;
		else if (key == "THREEPEATER_ULT_PROB_T3")
			g_threeUltProbT3 = val;
		else if (key == "THREEPEATER_ULT_PROB_T5")
			g_threeUltProbT5 = val;
		else if (key == "CORNPULT_BUTTER_BASE")
			g_cornButterBase = val;
		else if (key == "CORNPULT_BUTTER_UP")
			g_cornButterUp = val;
		else if (key == "CORNPULT_BUTTER_MAX")
			g_cornButterMax = val;
		else if (key == "CHOMPER_BITE_PERCENT")
			g_chomberBitePercent = val;
		else if (key == "MELON_CANNON_DAMAGE")
			g_melonCannonDamage = val;
		else if (key == "ICE_MELON_FREEZE_PROBABILITY")
			g_iceMelonFreezeProbability = (val < 0) ? 0 : ((val > 100) ? 100 : val);
		else if (key == "ICE_MELON_VOLLEY_COUNT")
			g_iceMelonVolleyCount = (val < 0) ? 0 : ((val > 60) ? 60 : val);
		else if (key == "SEASHROOM_POISON_STACK_T0")
			g_seaStackT0 = val;
		else if (key == "SEASHROOM_POISON_STACK_T1")
			g_seaStackT1 = val;
		else if (key == "SEASHROOM_POISON_STACK_T3")
			g_seaStackT3 = val;
		else if (key == "SEASHROOM_POISON_BURST_STACKS")
			g_seaBurstThreshold = val;
		else if (key == "SEASHROOM_TINT_ENABLED")
			g_poisonTintEnabled = (val != 0) ? 1 : 0;
		else if (key == "SEASHROOM_BURST_PARTICLE_ENABLED")
			g_seaBurstParticleEnabled = (val != 0) ? 1 : 0;
		else if (key == "SEASHROOM_BURST_EFFECT1")
			g_seaBurstEffect1 = val;
		else if (key == "TALLNUT_T1_MAXHP")
			g_tallnutT1MaxHp = (val < 1000) ? 1000 : val;   // 下限防呆：上限至少 1000
		else if (key == "TALLNUT_ANTIKILL_DAMAGE")
			g_tallnutAntiKillDmg = (val < 1) ? 1 : val;
		else if (key == "GARLIC_T1_MAXHP")
			g_garlicT1MaxHp = (val < 100) ? 100 : val;      // 下限防呆：上限至少 100
		// ---- 大喷菇（Fumeshroom）等阶机制 ----
		else if (key == "FUME_ENABLED")
			g_fumeEnabled = (val != 0) ? 1 : 0;
		else if (key == "FUME_T3_RANGE_EXTEND")
			g_fumeRangeExtend = (val < 0) ? 0 : ((val > 800) ? 800 : val);
		else if (key == "FUME_T3_PUFF_DX")
			g_fumeT3PuffDx = (val < 0) ? 0 : ((val > 600) ? 600 : val);
		else if (key == "FUME_KB_DISTANCE")
			g_fumeKbDistance = (val < 0) ? 0 : ((val > 200) ? 200 : val);
		else if (key == "FUME_KB_FRAMES")
			g_fumeKbFrames = (val < 1) ? 1 : ((val > 120) ? 120 : val);
		else if (key == "FUME_DEBUG")
			g_fumeDebug = (val != 0) ? 1 : 0;
		else if (key == "GARLIC_ARROW_OFFSET_X")
			g_garlicArrowOffX = val;
		else if (key == "GARLIC_ARROW_OFFSET_Y")
			g_garlicArrowOffY = val;
		else if (key == "GARLIC_DEBUG")
			g_garlicDebug = (val != 0) ? 1 : 0;
		else if (key == "GARLIC_ENABLED")
			g_garlicEnabled = (val != 0) ? 1 : 0;
		else if (key == "SEASHROOM_BURST_EFFECT2")
			g_seaBurstEffect2 = val;
		else if (key == "SEASHROOM_BURST_IMAGE1")
			g_seaBurstImage1 = val;
		else if (key == "SEASHROOM_BURST_IMAGE2")
			g_seaBurstImage2 = val;
		else if (key == "SEASHROOM_BURST_OFFSET_X")
			g_seaBurstOffsetX = val;
		else if (key == "SEASHROOM_BURST_OFFSET_Y")
			g_seaBurstOffsetY = val;
		else if (key == "SEASHROOM_BURST_TINT_R")
			g_seaBurstTintR = val;
		else if (key == "SEASHROOM_BURST_TINT_G")
			g_seaBurstTintG = val;
		else if (key == "SEASHROOM_BURST_TINT_B")
			g_seaBurstTintB = val;
		// ===== 究极大喷菇（基于大喷菇 SeedType=10 改造）=====
		else if (key == "ULF_ENABLED")
			g_ulfEnabled = (val != 0) ? 1 : 0;
		else if (key == "ULF_INTERVAL_CS")
			g_ulfIntervalCs = (val < 1) ? 1 : val;
		else if (key == "ULF_DAMAGE")
			g_ulfDamage = val;
		else if (key == "ULF_SLOW_CS")
			g_ulfSlowCs = val;
		else if (key == "ULF_FREEZE_GAIN")
			g_ulfFreezeGain = val;
		else if (key == "ULF_FREEZE_CAP_BASE")
			g_ulfFreezeCapBase = (val < 1) ? 1 : val;
		else if (key == "ULF_FREEZE_CAP_STEP")
			g_ulfFreezeCapStep = val;
		else if (key == "ULF_FREEZE_CAP_MAX")
			g_ulfFreezeCapMax = val;
		else if (key == "ULF_FREEZE_CS")
			g_ulfFreezeCs = val;
		else if (key == "ULF_CHARM_PERCENT")
			g_ulfCharmPercent = val;
		else if (key == "ULF_CHARM_HP_PERCENT")
			g_ulfCharmHpPercent = val;
		else if (key == "ULF_CHARM_TOTAL_HP")
			g_ulfCharmTotalHp = (val != 0) ? 1 : 0;
		else if (key == "ULF_BOOM_DAMAGE")
			g_ulfBoomDamage = val;
		else if (key == "ULF_BOOM_ROW_RANGE")
			g_ulfBoomRowRange = val;
		else if (key == "ULF_BOOM_X_RANGE")
			g_ulfBoomXRange = val;
		else if (key == "ULF_BOOM_SOUND")
			g_ulfBoomSound = val;
		else if (key == "ULF_FRONT_ONLY")
			g_ulfFrontOnly = (val != 0) ? 1 : 0;
		else if (key == "ULF_DEBUG")
			g_ulfDebug = (val != 0) ? 1 : 0;
		// ===== 寒冰菇（IceShroom, SeedType=14）机制 =====
		else if (key == "ICESHROOM_FREEZE_CS")
			g_iceFreezeCs = val;
		else if (key == "ICESHROOM_VULNERABLE_PERCENT")
			g_iceVulnPercent = val;
		else if (key == "ICESHROOM_FIELD_DURATION")
			g_iceFieldCs = val;
		// ===== 毁灭菇（DoomShroom, SeedType=15）领域粒子 =====
		else if (key == "DOOM_FIELD_EMBER_EFFECT")
			g_doomEmberEffect = val;
		else if (key == "DOOM_FIELD_DUST_EFFECT")
			g_doomDustEffect = val;
		else if (key == "DOOM_FIELD_FOG")
			g_doomFogEnabled = (val != 0) ? 1 : 0;
		// ===== 机枪射手（GatlingPea, SeedType=40）5阶大招 =====
		else if (key == "GATLING_ULT_EXP_COST")
			g_gatlingUltExpCost = (val < 1) ? 1 : val;
		else if (key == "GATLING_ULT_COUNT")
			g_gatlingUltCount = (val < 1) ? 1 : val;
		else if (key == "GATLING_ULT_DURATION_TICKS")
			g_gatlingUltDuration = (val < 1) ? 1 : val;
		else if (key == "GATLING_ULT_SPEED")
			g_gatlingUltSpeed = (float)std::atof(vstr.c_str());
		else if (key == "GATLING_ULT_SPREAD_DEG")
			g_gatlingUltSpreadDeg = (float)std::atof(vstr.c_str());
		else if (key == "GATLING_ULT_Y_RAND")
			g_gatlingUltYRand = (val < 0) ? 0 : val;
		// ===== 磁力菇（MagnetShroom, SeedType=31）等阶机制（3阶满阶，阈值见 plant_tier.ini 31= 行）=====
		else if (key == "MAGNET_SHIELD_HP")
			g_magShieldHp = (val < 1) ? 1 : val;
		else if (key == "MAGNET_RADIUS_BONUS")
			g_magRadiusBonus = (val < 0) ? 0 : val;
		else if (key == "MAGNET_THROW_DAMAGE")
			g_magThrowDamage = (val < 0) ? 0 : val;
		else if (key == "MAGNET_THROW_MS")
			g_magThrowMs = (val < 10) ? 10 : ((val > 350) ? 350 : val);
		else if (key == "MAGNET_LADDER_HP")
			g_magLadderHp = (val < 0) ? 0 : val;
		// ===== 墓碑吞噬者（GraveBuster, SeedType=11）等阶机制 =====
		else if (key == "GB_EXP_PACK_GAIN")
			g_gbExpPackGain = (val < 1) ? 1 : val;
		else if (key == "GB_DIG_EXP")
			g_gbDigExp = (val < 0) ? 0 : val;
		else if (key == "GB_ITEM_LIFE_CS")
			g_gbItemLifeCs = (val < 120) ? 120 : val;
		else if (key == "GB_ZOMBIE_TYPES")
		{
			int n = ParseIntList(vstr, g_gbZombieTypes, 8);
			if (n > 0) g_gbZombieTypeCount = n;
		}
		else if (key == "GB_CARD_EXCLUDE")
		{
			int n = ParseIntList(vstr, g_gbExcludeSeeds, 8);
			g_gbExcludeCount = n;   // 想"不排除任何植物"就写 -1（-1 本身不是有效种子）
		}
		else if (key == "GB_ITEM_ANIM_SPEED")
		{
			// 浮点：经验包"跳出"整体播放速度（1.0=原速，越小越慢；0.8 = 慢到 1.25 倍时长）
			float s = (float)std::atof(vstr.c_str());
			if (s < 0.2f) s = 0.2f;
			if (s > 3.0f) s = 3.0f;
			g_gbItemAnimSpeed = s;
		}
		else if (key == "GB_DEBUG")
			g_gbDebug = val;
		// 注：MAGNET_SHIELD_OFF_X / _Y 已于 2026-10-16 定稿并硬编码（常量 MAG_SHIELD_OFF_*），
		//     ini 里再写这两项也不会生效（已从配置文件移除）。
		//     MAGNET_DEBUG 自检日志已于 2026-10-16 随开发完成一并移除。
	}
	file.close();
}

void InitPlantExperience(DWORD plantAddress)
{
	if ((int)plantAddress < 0x10000)   // 拒绝 0/-1 等哨兵地址（防崩溃残留键）
		return;
	if (g_plantExperience.find(plantAddress) == g_plantExperience.end())
	{
		g_plantExperience[plantAddress] = 0;
	}
}

void RemovePlantExperience(DWORD plantAddress)
{
	auto it = g_plantExperience.find(plantAddress);
	if (it != g_plantExperience.end())
	{
		g_plantExperience.erase(it);
	}
	g_coffeeAwakenedPlants.erase(plantAddress);   // 咖啡豆唤醒标记随植物移除（防地址复用）
	MagOnPlantShieldRemoved(plantAddress);        // 磁力菇护盾：本格已经空了就立刻撤盾
	g_starfruitAttackCount.erase(plantAddress);
	g_cornPultHits.erase(plantAddress);           // 玉米投手每僵尸黄油计数（防地址复用）
	g_cornFrontDist.erase(plantAddress);          // 玉米投手距离缓存
	g_cornFrontZombie.erase(plantAddress);        // 玉米投手目标僵尸缓存
	// 三线射手大招状态清理（POD 数组，铲除/死亡即失效）
	for (int i = 0; i < 24; i++)
		if (g_tripleStates[i].plant == (DWORD)plantAddress)
			g_tripleStates[i].plant = 0;
}

// 把溢出经验瀑布式均分给同行(row)内其他未满经验的植物。
// 每轮按 pool/候选数 平均分配，吸满(达到上限)的植物在下一轮退出候选，
// 剩余经验继续均分给仍可吸收的植物，直到经验分完或再无候选。
// excludePlantAddress 为本轮已经吸满的植物，不参与分配。
//
// ★ 必须用 GetAllPlants() 遍历植物，绝对不能手工遍历 DataArray！
//    DataArray 是结构体数组(stride=0x14C)，不是指针数组。
//    手工用 plantArray + i*4 读到的是垃圾数据（已验证：i=2时读到0x78导致崩溃）。
void DistributeRowExperience(int row, DWORD excludePlantAddress, int pool)
{
	if (pool <= 0)
		return;

	int boardAddress = MemSafeRead<int>(PVZ_BASE + 0x768);
	if (boardAddress == 0)
		return;

	// 用 GetAllPlants() 而不是手工遍历 DataArray
	// DataArray 是结构体数组(stride=0x14C)，不是指针数组！
	PVZ::Board board(boardAddress);
	auto plants = board.GetAllPlants();

	while (pool > 0)
	{
		// 收集本行未满经验的植物
		std::vector<DWORD> candidates;
		for (auto& plant : plants)
		{
			int addr = plant.GetBaseAddress();
			if (addr == 0 || addr == (int)excludePlantAddress)
				continue;

			// 行号必须一致
			if ((int)plant.Row != row)
				continue;

			auto it = g_plantExperience.find(addr);
			if (it == g_plantExperience.end())
				continue;

			// 花盆/睡莲/南瓜头不参与经验分配
			if (IsNoTierPlant((int)plant.Type))
				continue;

			// 咖啡豆唤醒锁定的植物（保护伞等）未解锁前不参与经验分配
			if (!IsPlantExpUnlocked(addr, (int)plant.Type))
				continue;

			int limit = GetSeedExperienceLimit((int)plant.Type);
			// 机枪射手：满阶仍以"未满阶"身份参与经验分配（溢出由轮询帧转大招能量）
			bool gatlingSink = ((int)plant.Type == (int)SeedType::GatlingPea);
			if (it->second < limit || gatlingSink)
				candidates.push_back(addr);
		}

		if (candidates.empty())
			break;

		int n = (int)candidates.size();
		int base = pool / n;
		int rem = pool % n;

		// pool < n：余数即剩余经验，前 rem 个各 +1 后结束
		if (base == 0)
		{
			for (int i = 0; i < rem; i++)
				g_plantExperience[candidates[i]] += 1;
			break;
		}

		int poolLeft = pool;
		bool anyCapped = false;
		for (int i = 0; i < n; i++)
		{
			DWORD addr = candidates[i];
			int give = base + (i < rem ? 1 : 0);

			PVZ::Plant plant(addr);
			int limit = GetSeedExperienceLimit((int)plant.Type);
			int& exp = g_plantExperience[addr];

			// 机枪射手：满阶仍吸收（room 无上限；溢出由轮询帧转大招能量）
			int room = ((int)plant.Type == (int)SeedType::GatlingPea)
				? 0x7FFFFFFF : (limit - exp);
			if (give > room)
			{
				give = room;	// 截断到上限
				anyCapped = true;
			}
			exp += give;
			poolLeft -= give;
		}

		pool = poolLeft;		// 被截断后剩余的继续分给未满植物
		if (!anyCapped)			// 本轮无人被截断 => 全部分完
			break;
	}
}

void AddPlantExperience(DWORD plantAddress, int amount)
{
	if ((int)plantAddress < 0x10000)   // 拒绝 0/-1 等哨兵地址（防崩溃残留键）
		return;
	PVZ::Plant plant(plantAddress);
	if (!plant.isValid())
		return;

	int seedType = (int)plant.Type;

	// 花盆/睡莲/南瓜头没有等阶，不获得任何经验（连经验条目都不创建）
	if (IsNoTierPlant(seedType))
		return;

	// 咖啡豆唤醒锁定的植物（保护伞等）未解锁前不获得经验
	if (!IsPlantExpUnlocked(plantAddress, seedType))
		return;

	auto it = g_plantExperience.find(plantAddress);
	if (it == g_plantExperience.end())
	{
		InitPlantExperience(plantAddress);
		it = g_plantExperience.find(plantAddress);
		if (it == g_plantExperience.end())
			return;
	}

	int limit = GetSeedExperienceLimit(seedType);

	int& exp = it->second;

	// 机枪射手：经验吸收不设上限——满阶后继续吸收（不在此分流给同行），
	// 溢出部分由轮询帧 GatlingFrame 转入大招能量（每满 GATLING_ULT_EXP_COST 开一次大招）。
	// 满阶后仍以"未满阶"身份参与同行经验分配（DistributeRowExperience 候选特判）。
	if (seedType == (int)SeedType::GatlingPea)
	{
		exp += amount;
		return;
	}

	// 当前植物已满经验：全部经验均分给同行其他未满植物
	if (exp >= limit)
	{
		DistributeRowExperience((int)plant.Row, plantAddress, amount);
		return;
	}

	// 当前植物先吸收到上限
	int room = limit - exp;
	if (amount <= room)
	{
		exp += amount;
	}
	else
	{
		// 有溢出：当前植物吸满，剩余经验均分给同行其他未满植物
		exp = limit;
		int overflow = amount - room;
		DistributeRowExperience((int)plant.Row, plantAddress, overflow);
	}
}

// ==================== 经验包（肥料按钮）====================
// 交互链路：
//   点击按钮(Hook Board::MouseDown 0x411F20) → 选中/取消
//   选中状态下点击植物 → 扣阳光 + 加经验 + 进入冷却
// 绘制链路：
//   Hook Board::DrawUITop 入口(0x41AA40) 保存 Graphics* → onDrawUITop 绘制
//   （onDrawUITop 的 graphics 参数来自 DrawUITopEvent 的 [esp+40]，
//     该位置是调用者栈深处、不可靠，故由入口 hook 自行保存）

// 点在矩形内
static bool ExpPouchPointInRect(int rx, int ry, int rw, int rh, int x, int y)
{
	return x >= rx && x < rx + rw && y >= ry && y < ry + rh;
}

// 计算经验包按钮矩形：主菜单按钮(Widget)正下方，再按用户要求微调（左移20px 上移40px）
// 主菜单按钮 = Board+0x148，Widget 布局：mX=+0x0 mY=+0x4 mW=+0x8 mH=+0xC
// 读取失败或超出合理范围时回退到默认右上角位置 (742, 8, 60, 57) 下方
static void UpdateExpPouchButtonRect(int boardAddr)
{
	int btnX = 742, btnY = 8, btnH = 57;
	int menuBtn = boardAddr ? MemSafeRead<int>(boardAddr + 0x148) : 0;
	if (menuBtn)
	{
		int mx = MemSafeRead<int>(menuBtn + 0x0);
		int my = MemSafeRead<int>(menuBtn + 0x4);
		int mw = MemSafeRead<int>(menuBtn + 0x8);
		int mh = MemSafeRead<int>(menuBtn + 0xC);
		// 范围校验：主菜单按钮应位于屏幕右上角区域
		if (mx >= 600 && mx <= 790 && my >= 0 && my <= 120
			&& mw > 20 && mw < 120 && mh > 20 && mh < 120)
		{
			btnX = mx;
			btnY = my;
			btnH = mh;
		}
	}
	// 用户要求：左移 20px、上移 40px
	g_expPouchBtnX = btnX - 20;
	g_expPouchBtnY = (btnY + btnH + 8) - 40;  // 主菜单按钮下方 8px，再上移 40px
}

// 读取鼠标实时位置（从 Board::MouseMove hook 写入的堆内存读取，见 InstallExpPouchMouseMoveHook）
// 范围校验：坐标合法(0~800 / 0~600)才采用，非法时保留上次有效值（-1=从未获得）
static void ExpPouchUpdateMousePos()
{
	if (!g_expPouchMouseStore)
		return;
	__try
	{
		int mx = MemSafeRead<int>(g_expPouchMouseStore + 4);
		int my = MemSafeRead<int>(g_expPouchMouseStore);
		if (mx >= 0 && mx <= 800 && my >= 0 && my <= 600)
		{
			g_expPouchMouseX = mx;
			g_expPouchMouseY = my;
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		// 读取异常：保持上次值
	}
}

// 安装 Board::MouseMove hook @ 0x40E760，捕获鼠标实时坐标
// 反汇编确认 0x40E760：mov edx,[esp+8]; mov eax,[esp+4]; push esi; mov esi,[ecx+0x160]; call 0x421920; pop esi; ret 8
//   ★ 参数顺序（由 0x421920 参数布局反推）：0x421920 = Challenge::MouseMove(edx=y, eax=x, esi=this)
//   → Board 把 [esp+8] 装入 edx(y)、[esp+4] 装入 eax(x) → 入口实际 [esp+4]=x, [esp+8]=y（函数表写的 (y,x) 又是反的！）
// 方案：hook 入口把 (x,y) 写入堆内存 g_expPouchMouseStore（new DWORD[2]，A3 写堆绝对可写，同 g store 教训），不拦截直接放行
// trampoline 布局（PUSHAD 压 32 字节：原 [esp+4]=x → [esp+0x24]，原 [esp+8]=y → [esp+0x28]）:
//   [0x00] PUSHAD
//   [0x01] mov eax, [esp+0x24]    x
//   [0x05] mov [store+4], eax     存 x（moffs32）
//   [0x0A] mov eax, [esp+0x28]    y
//   [0x0E] mov [store], eax       存 y（moffs32）
//   [0x13] POPAD
//   [0x14] <原8字节>              mov edx,[esp+8]; mov eax,[esp+4]
//   [0x1C] jmp 0x40E768
void InstallExpPouchMouseMoveHook()
{
	DWORD hookAddr = 0x40E760;
	int rawLen = 8;  // 8B 54 24 08 8B 44 24 04（两条 mov，各 4 字节）
	BYTE rawCode[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, rawCode, rawLen);
	{
		static const BYTE kExpected[8] = { 0x8B, 0x54, 0x24, 0x08, 0x8B, 0x44, 0x24, 0x04 };
		if (memcmp(rawCode, kExpected, 8) != 0)
		{
			CrashStr("HOOKSKIP name=ExpPouchMouseMove site=0x40E760 (bytes changed - modifier?)\r\n");
			return;
		}
	}

	if (!g_expPouchMouseStore)
		g_expPouchMouseStore = (DWORD)new DWORD[2];  // 8 字节堆内存
	if (!g_expPouchMouseStore)
		return;

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return;

	BYTE tp[64];
	int p = 0;
	DWORD storeY = g_expPouchMouseStore;        // [store]   存 y
	DWORD storeX = g_expPouchMouseStore + 4;    // [store+4] 存 x
	tp[p++] = 0x60;                                      // PUSHAD
	tp[p++] = 0x8B; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x24; // mov eax, [esp+0x24] (x)
	tp[p++] = 0xA3; memcpy(tp + p, &storeX, 4); p += 4;    // mov [store+4], eax
	tp[p++] = 0x8B; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x28; // mov eax, [esp+0x28] (y)
	tp[p++] = 0xA3; memcpy(tp + p, &storeY, 4); p += 4;    // mov [store], eax
	tp[p++] = 0x61;                                      // POPAD
	memcpy(tp + p, rawCode, rawLen); p += rawLen;        // 原8字节
	int jmpOff = (int)(hookAddr + rawLen) - (tramp + p + 5);
	tp[p++] = 0xE9; memcpy(tp + p, &jmpOff, 4); p += 4;  // jmp back (0x40E768)

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);

	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);

}

// 画植物高亮框（围绕植物图片范围外扩 6px，黄色，与原按钮选中色一致）
// ★ 2026-08-05 用户要求改为"植物本体高亮"（铲子式：植物变白）——改用原生 plant+0x145 标志
//   （见 InstallExpPouchHighlightHook），此函数不再被调用，保留作备选
static DWORD ExpPouchFindPlantAtMouse(int boardAddr);  // 前向声明（定义在 ExpPouchFindPlantAt 之后）
static bool ExpPouchPixelToGrid(int boardAddr, int x, int y, int* outCol, int* outRow);  // 前向声明
static DWORD ExpPouchFindPlantAt(int boardAddr, int row, int col);  // 前向声明

// ===== 金盏花（Marigold）机制前向声明（定义见"金盏花形态产出物机制"段）=====
static int HandleMarigoldItemMouseDown(DWORD boardAddr, int x, int y);  // 产出物点击处理（MouseDown 回调用）
static int MgSelectedItemType();             // 当前选中产出物类型（-1=无），高亮判定用
static float MgBoostFactor(DWORD plantAddr); // 留声机攻速加成系数（1.0=无加成）
static void MgCleanupPlant(DWORD plant);     // 植物移除清理（产出物/加成/杀虫剂/形态记录）
static void MgResetAll();                    // 新关卡全量重置
static void DrawMarigoldUI();                // 产出物/选中/杀虫剂区域/加成指示绘制
static void UpdateMarigoldFrame(DWORD boardAddress);  // 每帧轮询入口
static void ExpPouchDrawPlantHighlight(DWORD plantAddr, DWORD g)
{
	__try
	{
		if (MemSafeRead<BYTE>(plantAddr + 0x141))  // NotExist
			return;
		int px = MemSafeRead<int>(plantAddr + 0x8);   // GameObject ImageX（屏幕像素）
		int py = MemSafeRead<int>(plantAddr + 0xC);   // ImageY
		int pw = MemSafeRead<int>(plantAddr + 0x10);  // Width
		int ph = MemSafeRead<int>(plantAddr + 0x14);  // Height
		if (pw <= 0 || pw > 400 || ph <= 0 || ph > 400)
			return;  // 尺寸异常跳过
		Draw::SetColor(255, 255, 0, g);
		Draw::DrawRect(px - 6, py - 6, pw + 12, ph + 12, g);
		Draw::SetColor(255, 255, 255, g);
		Draw::DrawRect(px - 3, py - 3, pw + 6, ph + 6, g);  // 双层框更醒目
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		// 高亮异常跳过，不崩溃
	}
}

// ★ 原生铲子式植物高亮（由 Board::DrawGameObjects 入口 hook 调用，绘制第一件事）
// 机制（反汇编确认）：
//   - 高亮标志 plant+0x145=1（HighlightPlantsForMouse 0x40E940 内部 MouseHitTest 0x411730 命中植物后设置）
//   - 清除：UpdateMousePosition(0x40EAB0) 每帧先遍历清所有植物 0x40EAEA mov [plant+0x145],0
//   - 读取：植物绘制处 0x463720 cmp [esi+0x145],0 → 非0 时叠加白色(0xff,0xff,0xc4)
// ★ 不直接调 HighlightPlantsForMouse（它内部依赖 Board+0x138 鼠标结构，此改版未验证），
//   改为自己 PixelToGrid 找植物 + 直接写 0x145（点击链路已验证这两步可靠）
static int __cdecl HandleExpPouchHighlight(DWORD boardAddr)
{
	__try
	{
		if (!boardAddr)
			return 0;
		// 仅选中（手持）状态下高亮鼠标下的植物；鼠标坐标未知（-1）跳过
		// 经验包 或 金盏花产出物（植物目标类 0/1/2）选中时都高亮
		if (!g_expPouchSelected && g_mgSelected < 0)
			return 0;
		// 杀虫剂（类型3）目标是格子：不高亮植物（格子效果由 Spray 动画指示，无自绘高亮）
		if (MgSelectedItemType() == 3)
			return 0;
		if (g_expPouchMouseX < 0 || g_expPouchMouseY < 0)
			return 0;
		// 暂停/选卡等状态下不处理（Board+0x164 = mPaused）
		if (MemSafeRead<BYTE>(boardAddr + 0x164))
			return 0;
		// 找鼠标下植物 → 写高亮标志（plant+0x145=1，原生铲子式：本体变白）
		// 清除由游戏自管（UpdateMousePosition 每帧清所有植物 0x145，无残留）
		DWORD plant = ExpPouchFindPlantAtMouse(boardAddr);
		if (plant && !MemSafeRead<BYTE>(plant + 0x141))  // NotExist
			MemSafeWrite<BYTE>(plant + 0x145, 1);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		// 绘制上下文调用可能触发访问违例被 SEH 吞掉，静默跳过即可
	}
	return 0;
}

// 安装 Board::DrawGameObjects 入口 hook @ 0x416880（植物绘制前设置高亮标志）
// 入口前 6 字节：55 8B EC 83 E4 F8（push ebp; mov ebp,esp; and esp,-8），同 MouseDown hook 模式
// ★ 调用约定（调用点 0x41AE33 反汇编确认，函数表是错的！）：push edi; push esi; call 0x416880
//   → 2 个栈参数：[esp+4]=esi=Board*（调用前 esi 被用作 Board：0x41AE04 mov [esi+0x5784],1），[esp+8]=edi=Graphics* g
//   → 不是 thiscall，this 不在 ecx！PUSHAD 后 Board* 在原 [esp+4] = [esp+0x24]
// trampoline:
//   [0x00] PUSHAD
//   [0x01] push [esp+0x24]     board（原 [esp+4] = esi 参数）
//   [0x05] call HandleExpPouchHighlight (__cdecl)
//   [0x0A] add esp, 4
//   [0x0D] mov [esp+0x1C], eax 写回 EAX 槽（保持一致）
//   [0x11] POPAD
//   [0x12] <原6字节>
//   [0x18] jmp 0x416886
void InstallExpPouchHighlightHook()
{
	DWORD hookAddr = 0x416880;
	int rawLen = 6;
	BYTE rawCode[6];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, rawCode, rawLen);
	{
		static const BYTE kExpected[6] = { 0x55, 0x8B, 0xEC, 0x83, 0xE4, 0xF8 };
		if (memcmp(rawCode, kExpected, 6) != 0)
		{
			CrashStr("HOOKSKIP name=ExpPouchHighlight site=0x416880 (bytes changed - modifier?)\r\n");
			return;
		}
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return;

	BYTE tp[64];
	int p = 0;
	tp[p++] = 0x60;                                      // PUSHAD
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x24; // push [esp+0x24] board（原[esp+4]=esi）
	int callOff = (int)&HandleExpPouchHighlight - (tramp + p + 5);
	tp[p++] = 0xE8; memcpy(tp + p, &callOff, 4); p += 4; // call HandleExpPouchHighlight
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;      // add esp, 4
	tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x1C; // mov [esp+0x1C], eax
	tp[p++] = 0x61;                                      // POPAD
	memcpy(tp + p, rawCode, rawLen); p += rawLen;        // 原6字节
	int jmpOff = (int)(hookAddr + rawLen) - (tramp + p + 5);
	tp[p++] = 0xE9; memcpy(tp + p, &jmpOff, 4); p += 4;  // jmp back (0x416886)

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);

	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);

}

// 施肥动画改用金盏花现成方案（MgPlayUseAnim + AnimationType::Fertilizer），
// 旧自绘"绿光晕+绿框"方案已废弃删除（2026-08-27）。

// 像素坐标 → 格子（调用游戏原生 Board::PixelToGridX/Y，自动处理泳池/屋顶场景）
// 调用约定（反汇编 0x41C4C0/0x41C550 确认）：
//   PixelToGridX: eax=X, ecx=Board → eax=列；  PixelToGridY: ecx=Y, edx=Board, eax=X → eax=行
// 地图外返回 -1
static bool ExpPouchPixelToGrid(int boardAddr, int x, int y, int* outCol, int* outRow)
{
	int col = -1, row = -1;
	// 注意：不能直接 call 0x41C4C0（MASM 会生成 E8 相对调用，偏移按 DLL 内地址计算导致错位），
	// 必须把绝对地址装入寄存器后间接调用
	__asm {
		mov eax, x
		mov ecx, boardAddr
		mov ebx, 0x41C4C0
		call ebx
		mov col, eax
	}
	__asm {
		mov ecx, y
		mov edx, boardAddr
		mov eax, x
		mov ebx, 0x41C550
		call ebx
		mov row, eax
	}
	if (col < 0 || row < 0 || col > 8 || row > 5)
		return false;
	*outCol = col;
	*outRow = row;
	return true;
}

// 查找指定格子上有等阶的植物（花盆/睡莲/南瓜头不计）
static DWORD ExpPouchFindPlantAt(int boardAddr, int row, int col)
{
	int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
	int plantCount = MemSafeRead<int>(boardAddr + 0xB0);
	if (!plantArray || plantCount <= 0)
		return 0;

	const DWORD PLANT_SIZE = 0x14C;
	for (int i = 0; i < plantCount; i++)
	{
		DWORD p = plantArray + i * PLANT_SIZE;
		if (MemSafeRead<BYTE>(p + 0x141))  // NotExist
			continue;
		int pRow = MemSafeRead<int>(p + 0x1C);
		int pCol = MemSafeRead<int>(p + 0x28);
		if (pRow != row || pCol != col)
			continue;
		int type = MemSafeRead<int>(p + 0x24);
		if (!IsNoTierPlant(type))
			return p;
	}
	return 0;
}

// 查找鼠标悬停的植物（用于选中状态下高亮预览；返回 0 = 无植物）
static DWORD ExpPouchFindPlantAtMouse(int boardAddr)
{
	int col = -1, row = -1;
	if (!ExpPouchPixelToGrid(boardAddr, g_expPouchMouseX, g_expPouchMouseY, &col, &row))
		return 0;
	return ExpPouchFindPlantAt(boardAddr, row, col);
}

// 经验包是否就绪：冷却结束 且 阳光足够
static bool ExpPouchIsReady(int boardAddr)
{
	PVZ::Board board(boardAddr);
	if (!board.GetBaseAddress())
		return false;
	if (board.PlayingTime < g_expPouchCooldownEnd)
		return false;
	if (board.Sun < g_expPouchSunCost)
		return false;
	return true;
}

// 使用经验包：扣阳光 + 加经验 + 进入冷却 + 播放施肥动画
// 前向声明：金盏花"使用效果动画"（定义见"金盏花形态产出物机制"段）
// type 0=肥料：创建 AnimationType::Fertilizer（ZenGarden_fertilizer.reanim）动画，
//   1.5 秒后由金盏花轮询自动 Die 清理（g_mgFxAnims）。经验包施肥动画复用此方案。
static void MgPlayUseAnim(int type, int cx, int cy, int layer);
static void ExpPouchUse(int boardAddr, DWORD plantAddr)
{
	PVZ::Board board(boardAddr);
	if (!board.GetBaseAddress())
		return;

	// 扣阳光
	board.Sun = board.Sun - g_expPouchSunCost;
	if (board.Sun < 0)
		board.Sun = 0;

	// 加经验（AddPlantExperience 内部处理满级溢出、无等阶植物过滤）
	AddPlantExperience(plantAddr, g_expPouchExpGain);

	// 进入冷却并取消选中
	g_expPouchCooldownEnd = board.PlayingTime + g_expPouchCooldownCs;
	g_expPouchSelected = false;

	// 施肥动画（★ 复用金盏花现成方案）：在目标植物中心播放 ZenGarden_fertilizer 动画
	__try
	{
		int tpx = MemSafeRead<int>(plantAddr + 0x8);
		int tpy = MemSafeRead<int>(plantAddr + 0xC);
		int tpw = MemSafeRead<int>(plantAddr + 0x10);
		int tph = MemSafeRead<int>(plantAddr + 0x14);
		int tlayer = MemSafeRead<int>(plantAddr + 0x20);
		if (tpw > 0 && tpw <= 400 && tph > 0 && tph <= 400)
			MgPlayUseAnim(0, tpx + tpw / 2, tpy + tph / 2, tlayer);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		// 动画创建异常：忽略（不影响加经验/扣阳光）
	}
}

// ===== 魅惑菇3阶：魅惑僵尸手动移动（点击处理，实现见后文"魅惑菇机制"段）=====
static int HypnoHandleMouseDown(DWORD boardAddr, int x, int y);
// 裂荚射手 5阶 右键切换状态（定义在 SplitPeaShoot 附近）
static void SplitPeaCycleForm(DWORD plant, DWORD boardAddr);

// Board::MouseDown hook 回调（__cdecl，参数：board, clickCount, y, x）
// 返回 1 = 已拦截（本次点击被经验包消费，跳过原版处理）；0 = 放行
// 主体包 __try/__except：异常时放行原版，绝不让游戏崩溃
static int __cdecl HandleExpPouchMouseDown(DWORD boardAddr, int clickCount, int y, int x)
{

	__try
	{
		if (!boardAddr)
			return 0;
		// 暂停/选卡等状态下不可操作（Board+0x164 = mPaused，指针表确认）
		if (MemSafeRead<BYTE>(boardAddr + 0x164))
			return 0;

		// 西瓜升级路线选择窗口激活：按钮命中→选路线；其他左键→全部吞掉（模态窗口）
		// （内部放行右上角主菜单按钮，允许选择期间暂停）
		if (HandleMelonChooserMouseDown(boardAddr, x, y))
			return 1;

		// 仅左键（单击 1 / 双击 2）
		if (clickCount != 1 && clickCount != 2)
			return 0;

		UpdateExpPouchButtonRect(boardAddr);

		// 0) 金盏花产出物交互：单击拾起 → 拖动 → 单击目标生效（优先于经验包，防误触）
		if (HandleMarigoldItemMouseDown(boardAddr, x, y))
			return 1;

		// 0.5) 墓碑吞噬者产出的经验包：拾起 → 拖到植物上 +经验（同金盏花交互范式）
		if (GbHandleMouseDown(boardAddr, x, y))
			return 1;

		// 1) 点击经验包按钮：选中 / 再点取消
		if (ExpPouchPointInRect(g_expPouchBtnX, g_expPouchBtnY, 70, 72, x, y))
		{
			if (g_expPouchSelected)
			{
				g_expPouchSelected = false;   // 取消选中
			}
			else if (ExpPouchIsReady(boardAddr))
			{
				g_expPouchSelected = true;    // 选中（冷却中/阳光不足时不选中）
				g_mgSelected = -1;            // 与金盏花产出物互斥
			}
			return 1;  // 拦截：按钮区域原版无操作，直接消费
		}

		// 2) 选中状态下点击植物 → 使用经验包；点空地/其它 → 肥料放回原处（取消选中）
		if (g_expPouchSelected)
		{
			int col = -1, row = -1;
			if (ExpPouchPixelToGrid(boardAddr, x, y, &col, &row))
			{
				DWORD plant = ExpPouchFindPlantAt(boardAddr, row, col);
				if (plant)
				{
					ExpPouchUse(boardAddr, plant);
					return 1;  // 拦截：经验包已消费本次点击
				}
			}
			// 点击空地/非植物：肥料放回按钮原处（取消选中），同铲子收起行为
			g_expPouchSelected = false;
			return 1;  // 拦截：本次点击已用于收起经验包
		}

		// 3) 魅惑菇3阶：魅惑僵尸选中/移动（经验包未选中时才处理，避免相互抢点击）
		if (HypnoHandleMouseDown(boardAddr, x, y))
			return 1;

		// 裂荚射手 5阶 切换状态已改为右键（见 UpdateMarigoldFrameInner 右键检测段）
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		// 异常：放行原版
		return 0;
	}

	return 0;
}

// 安装经验包交互 hook @ Board::MouseDown (0x411F20)
// 调用约定（反汇编 0x411F20 确认）：入口 [esp+4]=theClickCount, [esp+8]=y, [esp+0xC]=x，ecx=Board*
// 原函数为虚函数，被调用者清栈 ret 0xC（3 参数）。
// ★ 入口前 6 字节是完整指令边界：55 8B EC 83 E4 F8 (push ebp; mov ebp,esp; and esp,-8)
//   rawLen 必须取 6（不能只取 5，否则 jmp back 落在 and esp,-8 的 imm8 上，栈对齐被破坏）
// trampoline 布局（PUSHAD 压 32 字节：原 ecx 在 [esp+0x18]，原参数在 [esp+0x24/0x28/0x2C]）:
//   [0x00] PUSHAD
//   [0x01] push [esp+0x2C]  x          (原 [E+0x2C])
//   [0x05] push [esp+0x2C]  y          (第2次 push 后读 [E+0x28])
//   [0x09] push [esp+0x34]  clickCount (第3次 push 后读 [E+0x2C])
//   [0x0D] push [esp+0x24]  board      (第4次 push 后读 [E-0xC+0x24]=[E+0x18]=原ecx)
//   [0x11] call HandleExpPouchMouseDown (__cdecl)
//   [0x16] add esp, 0x10
//   [0x19] mov [esp+0x1C], eax         写回 PUSHAD 的 EAX 槽
//   [0x1D] POPAD
//   [0x1E] test eax, eax
//   [0x20] jnz +0x0B                    → [0x2D] 拦截分支
//   [0x22] <原6字节>
//   [0x28] jmp 0x411F26                 （占5字节）
//   [0x2D] ret 0xC                      拦截：清3参数返回（与原函数一致）
void InstallExpPouchMouseHook()
{
	DWORD hookAddr = 0x411F20;
	int rawLen = 6;
	BYTE rawCode[6];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, rawCode, rawLen);
	{
		static const BYTE kExpected[6] = { 0x55, 0x8B, 0xEC, 0x83, 0xE4, 0xF8 };
		if (memcmp(rawCode, kExpected, 6) != 0)
		{
			CrashStr("HOOKSKIP name=ExpPouchMouse site=0x411F20 (bytes changed - modifier?)\r\n");
			return;
		}
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return;

	BYTE tp[64];
	int p = 0;
	// ★ 参数映射（反汇编+实测日志确认，函数表 (theClickCount,y,x) 是错的！）：
	//   入口 [esp+4]=鼠标X, [esp+8]=鼠标Y, [esp+0xC]=clickCount（1=左键），ecx=Board*
	tp[p++] = 0x60;                                      // PUSHAD
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x24; // push [esp+0x24] x      (原[esp+4]=鼠标X)
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x2C; // push [esp+0x2C] y      (第2次push后读[E+0x28]=原[esp+8]=鼠标Y)
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x34; // push [esp+0x34] clickCount (第3次push后读[E+0x2C]=原[esp+0xC])
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x24; // push [esp+0x24] board  (第4次push后读[E-0xC+0x24]=[E+0x18]=原ecx)
	int callOff = (int)&HandleExpPouchMouseDown - (tramp + p + 5);
	tp[p++] = 0xE8; memcpy(tp + p, &callOff, 4); p += 4; // call HandleExpPouchMouseDown
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x10;      // add esp, 0x10
	tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x1C; // mov [esp+0x1C], eax
	tp[p++] = 0x61;                                      // POPAD
	tp[p++] = 0x85; tp[p++] = 0xC0;                      // test eax, eax
	tp[p++] = 0x75; tp[p++] = 0x0B;                      // jnz +0x0B → [0x2D] 拦截
	memcpy(tp + p, rawCode, rawLen); p += rawLen;        // 原6字节
	int jmpOff = (int)(hookAddr + rawLen) - (tramp + p + 5);
	tp[p++] = 0xE9; memcpy(tp + p, &jmpOff, 4); p += 4;  // jmp back (0x411F26)
	tp[p++] = 0xC2; tp[p++] = 0x0C; tp[p++] = 0x00;      // [0x2D] ret 0xC（拦截返回）

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);

	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
}

// 安装 DrawUITop 入口 hook @ Board::DrawUITop (0x41AA40)
// 仅保存 Graphics* 到 g_drawUITopGraphics 供 onDrawUITop 绘制使用。
// ★ 调用约定（反汇编 0x41AA40 确认，函数表是错的！）：
//   入口 [esp+4] = Board* this，[esp+8] = Graphics* g
//   （0x41AA5D mov ebp,[esp+0x98] → 0x41AA64 mov eax,[ebp+0x8C]=LawnApp 证明 [esp+4] 是 Board）
//   因此 Graphics* 必须取 [esp+8]（PUSHAD 后 [esp+0x28]）；取 [esp+4] 会把 Board 当 Graphics 崩溃！
// ★ 入口前 8 字节是完整指令边界：6A FF 64 A1 00 00 00 00
//   (push -1; mov eax, fs:[0] —— mov eax,fs:[0] 是 6 字节指令！)
//   rawLen 必须取 8，否则 jmp back 落在 mov 指令中间导致崩溃。
// ★★ A3 写入目标用【堆内存地址】（g_expPouchGStore = new DWORD，绝对可写）：
//    实测 &g_drawUITopGraphics 打印为 0x586601AC（落在游戏 .text 只读段），
//    trampoline 的 A3 mov [绝对地址] 写它 → 访问违例 → EIP 停在 trampoline+5 崩溃。
//    改写入堆地址后 DrawExpPouchUI 从堆读，彻底绕开 DLL 静态变量地址问题。
void InstallExpPouchDrawHook()
{

	// 分配 4 字节可写堆内存存 Graphics*（new DWORD 的地址属于堆，可写）
	if (g_expPouchGStore == 0)
		g_expPouchGStore = (DWORD)new DWORD;
	if (g_expPouchGStore == 0)
		return;
	DWORD storeAddr = g_expPouchGStore;

	DWORD hookAddr = 0x41AA40;
	int rawLen = 8;
	BYTE rawCode[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, rawCode, rawLen);
	{
		static const BYTE kExpected[8] = { 0x6A, 0xFF, 0x64, 0xA1, 0x00, 0x00, 0x00, 0x00 };
		if (memcmp(rawCode, kExpected, 8) != 0)
		{
			CrashStr("HOOKSKIP name=ExpPouchDraw site=0x41AA40 (bytes changed - modifier?)\r\n");
			return;
		}
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return;

	BYTE tp[48];
	int p = 0;
	tp[p++] = 0x60;                                      // PUSHAD
	tp[p++] = 0x8B; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x28; // mov eax, [esp+0x28] (原[esp+8]=Graphics* g)
	tp[p++] = 0xA3;                                      // mov [storeAddr], eax (moffs32 = 堆地址)
	memcpy(tp + p, &storeAddr, 4); p += 4;               // ★ 写入堆地址值（可写），不是 &g_drawUITopGraphics！
	tp[p++] = 0x61;                                      // POPAD
	memcpy(tp + p, rawCode, rawLen); p += rawLen;        // 原8字节
	int jmpOff = (int)(hookAddr + rawLen) - (tramp + p + 5);
	tp[p++] = 0xE9; memcpy(tp + p, &jmpOff, 4); p += 4;  // jmp back (0x41AA48)

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);

	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);

}

// 校验 Graphics* 有效性：其虚表指针应位于代码/数据段（防无效 g 调用绘制函数崩溃）
// ★ Graphics* 是游戏堆对象（实测 = 0x1AFA98，32 位进程堆区），地址下限必须放宽到 0x10000，
//   不能按"游戏代码段 0x400000+"判断（那样会把合法 Graphics* 误杀导致按钮不绘制）
static bool ExpPouchGraphicsValid(DWORD g)
{
	if (g < 0x10000 || g > 0x7FFFFFFF)
		return false;
	__try
	{
		DWORD vtbl = MemSafeRead<DWORD>(g);
		return vtbl >= 0x400000 && vtbl < 0x900000;
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		return false;
	}
}

// 加载经验包图片（ShovelBank 背景 / Fertilizer 图标 / 冷却遮罩）
// __try 防护资源系统未就绪时的异常；内部只用内置类型 + FILE*（避免 C++ 对象展开与 SEH 冲突）
// ★★ 2026-10-16 修两处：
//   ① **不许失败后每帧重试**。原实现异常时把 g_expPouchImagesLoaded 复位成 false
//      → 下一帧又跑一遍 → 每帧泄漏 4 个 PVZ 字符串对象（Draw::ToString = AllocMemory(0,0x1C)
//        = new BYTE[1052]，调用方不释放）+ 每次都在游戏堆里建 std::string。
//      实测证据：D:\pvz_crash.log 里同一会话连续 12 条
//        `code=E06D7363（C++ 异常） step=exppouch:images`，且栈上有 std::bad_alloc 的
//        vtable 与 "bad allocation" 字样 ⇒ 就是这条重试循环把堆吃干后 operator new 抛的。
//      → 改成"只尝试一次"，失败就永久标记（记一行日志），不再重试。
//   ② 失败与成功都记一行（便于判断贴图到底有没有加载出来）。
static bool g_expPouchImagesTried = false;   // 本进程只尝试一次（成功/失败都不再重试）

static void LoadExpPouchImages()
{
	__try
	{
		DWORD isNew = 0;

		Draw::PString fnBank = Draw::ToString("images\\ShovelBank.png");
		Draw::PString variant = Draw::ToString("");
		DWORD refBank = Draw::GetSharedImage(isNew, variant, fnBank);
		if (refBank != 0)
			g_expPouchBankImage = Draw::SharedImageRefToImage(refBank);

		Draw::PString fnIcon = Draw::ToString("images\\Fertilizer.png");
		DWORD refIcon = Draw::GetSharedImage(isNew, variant, fnIcon);
		if (refIcon != 0)
			g_expPouchIconImage = Draw::SharedImageRefToImage(refIcon);

		Draw::PString fnOverlay = Draw::ToString("images\\ExpPouchCooldown.png");
		DWORD refOverlay = Draw::GetSharedImage(isNew, variant, fnOverlay);
		if (refOverlay != 0)
			g_expPouchOverlayImage = Draw::SharedImageRefToImage(refOverlay);

		CrashStr("[EXPPOUCH] images loaded\r\n");
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		// 图片加载异常：保持 0（绘制时自动跳过）。★ 绝不复位 g_expPouchImagesLoaded
		//（那会变成每帧重试 + 每帧泄漏 → 堆耗尽 → std::bad_alloc/随机 AV）。
		CrashStr("[EXPPOUCH] image load FAILED (permanently skipped)\r\n");
	}
}

// 绘制经验包 UI（由 onDrawUITop 调用，顶层 UI 末尾时机）
// 使用 g_drawUITopGraphics（DrawUITop 入口 hook 保存的本帧 Graphics*）
// 主体包 __try/__except：绘制异常只记录并跳过，绝不导致游戏崩溃
static void DrawExpPouchUI()
{
	// 防御性校验：g 必须是有效 Graphics*（虚表指针在代码/数据段），
	// 无效时静默跳过，绝不调用游戏绘制函数（防止 hook 参数取错导致崩溃）
	// g 从堆存储读取（trampoline 写入的堆地址，见 InstallExpPouchDrawHook）
	DWORD g = (g_expPouchGStore != 0)
		? MemSafeRead<DWORD>(g_expPouchGStore) : 0;


	if (!g || !ExpPouchGraphicsValid(g))
		return;

	__try
	{
		// 与 onDrawExpUI 相同的基址检查模式：LawnApp 未就绪时不绘制
		int pvzBase = MemSafeRead<int>(0x6A9EC0);
		if (pvzBase < 0x400000)
			return;

		int boardAddr = MemSafeRead<int>(pvzBase + 0x768);
		if (!boardAddr)
			return;

		// 禅境花园(0x2B)/智慧树(0x32)等模式不显示
		int gameMode = MemSafeRead<int>(pvzBase + 0x7F8);
		if (gameMode == 0x2B || gameMode == 0x32)
			return;

		UpdateExpPouchButtonRect(boardAddr);
		ExpPouchUpdateMousePos();


		int bx = g_expPouchBtnX;
		int by = g_expPouchBtnY;

		// 背景框（ShovelBank 70x72）
		if (g_expPouchBankImage)
			Draw::DrawImage(bx, by, g_expPouchBankImage, g);

		if (g_expPouchSelected)
		{
			// 选中状态：肥料"拿起"，图标跟随鼠标（Fertilizer 80x80，鼠标居中）
			if (g_expPouchIconImage && g_expPouchMouseX >= 0 && g_expPouchMouseY >= 0)
				Draw::DrawImage(g_expPouchMouseX - 40, g_expPouchMouseY - 40, g_expPouchIconImage, g);

			// 植物本体高亮（铲子式：植物变白）由 DrawGameObjects 入口 hook 设置原生 plant+0x145 标志，
			// 绘制时游戏自动叠加白色（见 InstallExpPouchHighlightHook），此处无需再画框
		}
		else
		{
			// 未选中：肥料图标放按钮框内（80x80 居中：x-5, y-4）
			if (g_expPouchIconImage)
				Draw::DrawImage(bx - 5, by - 4, g_expPouchIconImage, g);
		}

		// 按钮选中高亮（黄色边框）
		if (g_expPouchSelected)
		{
			Draw::SetColor(255, 255, 0, g);
			Draw::DrawRect(bx - 3, by - 3, 76, 78, g);
		}

		// 冷却遮罩 + 进度条（PlayingTime 直接读内存，避免 C++ 对象与 SEH 冲突）
		int playingTime = MemSafeRead<int>(boardAddr + 0x5568);
		int remain = g_expPouchCooldownEnd - playingTime;
		if (remain > 0)
		{
			// 半透明遮罩使图标变暗
			if (g_expPouchOverlayImage)
				Draw::DrawImage(bx, by, g_expPouchOverlayImage, g);

			// 黑色填充条指示冷却进度
			// ★ 2026-08-05 用户反馈：原"贴底部填充"视觉是黑条从上往下滑（顶部先露出），方向反了。
			//   改为贴顶部填充：黑条下边缘随时间上移，底部先恢复 → "从下往上滑" ✓
			if (g_expPouchCooldownCs > 0)
			{
				int fillH = 72 * remain / g_expPouchCooldownCs;
				if (fillH > 72) fillH = 72;
				if (fillH > 0)
				{
					Draw::SetColor(0, 0, 0, g);
					Draw::FillRect(bx, by, 70, fillH, g);
				}
			}
		}

	// 施肥动画由金盏花方案 MgPlayUseAnim 播放（ExpPouchUse 触发），此处无需自绘
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		// 绘制异常静默跳过（不崩溃）
	}
}

// ==================== DLL 导出函数 ====================

// 当前正在绘制的子弹的染色颜色指针（0=不染色）；游戏绘制为单线程，
// 46E6C7 trampoline 先写入、同帧 46E805 trampoline 读取，跨 hook 共享安全
static DWORD g_peaActiveColor = 0;

// 由 46E6C7（Projectile::Draw 内，esi=Projectile 可靠点）trampoline 每子弹调用：
// 读 [proj+0x8C] 染色标记 → 翻译成颜色指针存 g_peaActiveColor（供 46E805 绘制消费）
// 1=弱火(淡橙黄) 2=炎(炽红) 3=冰火(冰蓝)，其余=0 不染色
static void UpdatePeaActiveColor(DWORD projAddr)
{
	DWORD color = 0;
	if (projAddr)
	{
		int mark = MemSafeRead<int>(projAddr + 0x8C);
		if (mark == 1)      color = (DWORD)&g_peaWeakFireColor;
		else if (mark == 2) color = (DWORD)&g_peaBlazeColor;
		else if (mark == 3) color = (DWORD)&g_peaIceFireColor;
	}
	g_peaActiveColor = color;
}

void onDrawExpUI(DWORD gridItem); // 前向声明

// 安装寒冰射手自定义子弹贴图替换 hook @ 0x46E6C7
// 延迟到游戏代码解密完成后调用（init() 过早，直接开 pvzmain 时读到垃圾原代码会崩溃）
// 双标记：90=冰锥(5阶)，91=雪晶(3/4阶冻结子弹)
// ★ 2026-08-28 扩展：此点 esi=Projectile（可靠），trampoline 开头追加"染色记录段"
//   （pushad/push esi/call UpdatePeaActiveColor/popad），把 [proj+0x8C] 染色标记翻译成
//   颜色指针存 g_peaActiveColor，供 46E805（颜色参数 push 处，esi 已被覆盖不可靠）消费。
// trampoline 布局:
//   [0]  pushad                          (1字节) 染色记录段开始
//   [1]  push esi                        (1字节)
//   [2]  call UpdatePeaActiveColor       (5字节)
//   [7]  add esp, 4                      (3字节)
//   [10] popad                           (1字节) 染色记录段结束
//   [11] cmp dword [esi+0x78], 90        (7字节)
//   [18] je ICE  (+16)                   (2字节) → [36]
//   [20] cmp dword [esi+0x78], 91        (7字节)
//   [27] jne MELON (+20)                 (2字节) → [49]
//   [29] mov eax, [&g_snowCrystalImageAddr] (5字节)
//   [34] jmp APPLY (+5)                  (2字节) → [41]
//   [36] ICE: mov eax, [&g_icicleImageAddr] (5字节)
//   [41] APPLY: test eax, eax            (2字节) 空指针保护
//   [43] je MELON (+4)                   (2字节) → [49]
//   [45] mov [esp+0x0C], eax             (4字节) 替换绘制贴图指针
//   [49] MELON: cmp dword [esi+0x78], 95 (7字节)  92-94 是裂荚 [proj+0x80] 通道的标记数字，
//   [56] jne ISMALL (+13)                (2字节) → [71]   与 0x78 通道的 95 无冲突
//   [58] mov eax, [&g_melonBigImageAddr] (5字节)
//   [63] test eax, eax                   (2字节)
//   [65] je ISMALL (+4)                  (2字节) → [71]
//   [67] mov [esp+0x0C], eax             (4字节) 替换绘制贴图指针（放大版西瓜弹）
//   [71] ISMALL: cmp dword [esi+0x78], 96 (7字节) 小冰瓜（5阶冰西瓜大招散射弹）
//   [78] jne KB (+13)                    (2字节) → [93]（非小冰瓜继续判击退弹）
//   [80] mov eax, [&g_iceMelonSmallImageAddr] (5字节)
//   [85] test eax, eax                   (2字节)
//   [87] je ORIG (+4)                    (2字节) → [93]
//   [89] mov [esp+0x0C], eax             (4字节) 替换绘制贴图指针（80% 小冰瓜）
//   [93] KB: cmp dword [esi+0x78], 97    (7字节) 击退弹（豌豆射手3阶+）
//   [100] jne ORIG (+13)                 (2字节) → [115]
//   [102] mov eax, [&g_knockbackPeaImageAddr] (5字节)
//   [107] test eax, eax                  (2字节)
//   [109] je ORIG (+4)                   (2字节) → [115]
//   [111] mov [esp+0x0C], eax            (4字节) 替换绘制贴图指针
//   [115] ORIG: <原5字节>
//   [120] jmp back
void InstallIcicleImageHook()
{
	DWORD hookAddr = 0x46E6C7;
	int rawLen = 5;
	BYTE rawCode[5];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, rawCode, rawLen);
	{
		static const BYTE kExpected[5] = { 0xC6, 0x44, 0x24, 0x20, 0x00 };
		if (memcmp(rawCode, kExpected, 5) != 0)
		{
			CrashStr("HOOKSKIP name=IcicleImage site=0x46E6C7 (bytes changed - modifier?)\r\n");
			return;
		}
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp != 0)
	{
		if (rawCode[0] == 0xE8 || rawCode[0] == 0xE9)
			// 原代码位于 trampoline 偏移 115 处（11字节染色记录段 + 27 + 28 + 22 + 27）
			*(int*)(rawCode + 1) = *(int*)(rawCode + 1) + (int)hookAddr - tramp - 115;

		BYTE tp[128];
		int p = 0;
		auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
		// rel32 用 DWORD 无符号运算：VirtualAlloc 可能返回高地址（int 视为负数）会溢出
		auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

		// ---- 染色记录段（所有子弹必经）----
		tp[p++] = 0x60;                    // pushad
		tp[p++] = 0x56;                    // push esi（子弹地址）
		putRelCall((DWORD)&UpdatePeaActiveColor);
		tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;  // add esp, 4
		tp[p++] = 0x61;                    // popad

		// ---- 原冰锥/雪晶贴图替换逻辑 ----
		// cmp dword [esi+0x78], 90
		tp[p++] = 0x81; tp[p++] = 0x7E; tp[p++] = 0x78;
		*(DWORD*)(tp + p) = 90; p += 4;
		// je +16 → ICE（标记90 = 冰锥）
		tp[p++] = 0x74; tp[p++] = 0x10;
		// cmp dword [esi+0x78], 91
		tp[p++] = 0x81; tp[p++] = 0x7E; tp[p++] = 0x78;
		*(DWORD*)(tp + p) = 91; p += 4;
		// jne +20 → ORIG（非寒冰射手子弹）
		tp[p++] = 0x75; tp[p++] = 0x14;
		// mov eax, [&g_snowCrystalImageAddr]（雪晶贴图）
		tp[p++] = 0xA1; *(DWORD*)(tp + p) = (DWORD)&g_snowCrystalImageAddr; p += 4;
		// jmp +5 → APPLY
		tp[p++] = 0xEB; tp[p++] = 0x05;
		// ICE: mov eax, [&g_icicleImageAddr]（冰锥贴图）
		tp[p++] = 0xA1; *(DWORD*)(tp + p) = (DWORD)&g_icicleImageAddr; p += 4;
		// APPLY: test eax, eax; je +4 → 贴图未加载时跳过替换
		tp[p++] = 0x85; tp[p++] = 0xC0;
		tp[p++] = 0x74; tp[p++] = 0x04;
		// mov [esp+0x0C], eax（替换绘制贴图指针）
		tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x0C;
		// ---- 西瓜大炮弹贴图替换段（标记95）----
		// MELON: cmp dword [esi+0x78], 95（5阶西瓜投手大炮弹）
		tp[p++] = 0x81; tp[p++] = 0x7E; tp[p++] = 0x78;
		*(DWORD*)(tp + p) = 95; p += 4;
		// jne +13 → ISMALL（非大炮弹，继续判小冰瓜）
		tp[p++] = 0x75; tp[p++] = 0x0D;
		// mov eax, [&g_melonBigImageAddr]（放大版西瓜弹贴图）
		tp[p++] = 0xA1; *(DWORD*)(tp + p) = (DWORD)&g_melonBigImageAddr; p += 4;
		// test eax, eax; je +4 → 贴图未加载时跳过替换
		tp[p++] = 0x85; tp[p++] = 0xC0;
		tp[p++] = 0x74; tp[p++] = 0x04;
		// mov [esp+0x0C], eax（替换绘制贴图指针）
		tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x0C;
		// ---- 小冰瓜贴图替换段（标记96，5阶冰西瓜大招散射弹 80% 贴图）----
		// ISMALL: cmp dword [esi+0x78], 96
		tp[p++] = 0x81; tp[p++] = 0x7E; tp[p++] = 0x78;
		*(DWORD*)(tp + p) = 96; p += 4;
		// jne +13 → ORIG（非小冰瓜）
		tp[p++] = 0x75; tp[p++] = 0x0D;
		// mov eax, [&g_iceMelonSmallImageAddr]
		tp[p++] = 0xA1; *(DWORD*)(tp + p) = (DWORD)&g_iceMelonSmallImageAddr; p += 4;
		// test eax, eax; je +4 → 贴图未加载时跳过替换
		tp[p++] = 0x85; tp[p++] = 0xC0;
		tp[p++] = 0x74; tp[p++] = 0x04;
		// mov [esp+0x0C], eax（替换绘制贴图指针）
		tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x0C;
		// ---- 击退弹贴图替换段（标记97，豌豆射手3阶+）----
		// KB: cmp dword [esi+0x78], 97
		tp[p++] = 0x81; tp[p++] = 0x7E; tp[p++] = 0x78;
		*(DWORD*)(tp + p) = 97; p += 4;
		// jne +13 → ORIG（非击退弹）
		tp[p++] = 0x75; tp[p++] = 0x0D;
		// mov eax, [&g_knockbackPeaImageAddr]
		tp[p++] = 0xA1; *(DWORD*)(tp + p) = (DWORD)&g_knockbackPeaImageAddr; p += 4;
		// test eax, eax; je +4 → 贴图未加载时跳过替换
		tp[p++] = 0x85; tp[p++] = 0xC0;
		tp[p++] = 0x74; tp[p++] = 0x04;
		// mov [esp+0x0C], eax（替换绘制贴图指针）
		tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x0C;
		// ORIG: 原代码
		memcpy(tp + p, rawCode, rawLen); p += rawLen;
		// jmp back
		int jmpOff = (int)(hookAddr + rawLen) - (tramp + p + 5);
		tp[p++] = 0xE9; memcpy(tp + p, &jmpOff, 4); p += 4;

		PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);

		int hookOff = tramp - ((int)hookAddr + 5);
		BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
		PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	}
}

// 安装豌豆染色 hook @ 0x46E805（Projectile::Draw 主贴图绘制的颜色指针 push 处）
// 原代码: push 0072289C（5字节 68 9C 28 72 00，DrawImage 颜色参数=全局白）
// 延迟到游戏代码解密完成后调用（同 InstallIcicleImageHook，init() 过早会读到垃圾原代码）
// 原理（参考 S6 CE 表"灵魂子弹颜色"）：DrawImage 直接用调用者 push 的颜色指针做乘色，
//   替换颜色指针即可让子弹贴图整体偏色。火球贴图乘淡橙黄→弱火、乘炽红→炎、乘冰蓝→冰火。
// ★ 2026-08-28 修复（染色无效根因）：
//   Projectile::Draw 入口 @ 0x46E460 是 push ecx/push esi/push edi（不建 ebp 帧），
//   46E805 处 [ebp+8]/[ebp+C] 是调用者栈残留垃圾，esi 也在 46E7E1/46E7FB 被覆盖 →
//   原方案读 [ebp+0x94]/[ebp+0xA0] 取标记/Type 完全不可靠（[ebp+0x94] 常为 0 → 全走 ORIG）。
//   修复：染色标记→颜色指针的翻译移到 46E6C7（esi=Projectile 可靠点，冰锥 hook 处），
//   结果存全局 g_peaActiveColor；本 hook 只读全局 push（同帧同子弹，绘制单线程安全）。
// trampoline 布局：
//   [0]  A1 <&g_peaActiveColor>   mov eax, [&g_peaActiveColor]  (5字节)
//   [5]  85 C0                    test eax, eax                 (2字节)
//   [7]  74 ??                    je ORIG                       (2字节)
//   [9]  50                       push eax（染色颜色指针）      (1字节)
//   [10] EB ??                    jmp BACK                      (2字节)
//   [12] ORIG: 68 9C 28 72 00     push 0072289C                 (5字节)
//   [17] BACK: E9 <rel32>         jmp 0x46E80A                  (5字节)
void InstallPeaColorHook()
{
	DWORD hookAddr = 0x46E805;
	BYTE rawCode[5];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, rawCode, 5);
	{
		static const BYTE kExpected[5] = { 0x68, 0x9C, 0x28, 0x72, 0x00 };
		if (memcmp(rawCode, kExpected, 5) != 0)
		{
			CrashStr("HOOKSKIP name=PeaColor site=0x46E805 (bytes changed - modifier?)\r\n");
			return;
		}
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp != 0)
	{
		BYTE tp[48];
		int p = 0;
		auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
		// rel32 用 DWORD 无符号运算：VirtualAlloc 可能返回高地址（int 视为负数）会溢出
		auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
		// 回填 rel8 用的小工具
		auto fillJ8 = [&](int pos, int target) { *(BYTE*)(tp + pos + 1) = (BYTE)(target - (pos + 2)); };

		// mov eax, [&g_peaActiveColor]（当前子弹染色颜色指针，0=不染）
		tp[p++] = 0xA1; put32((int)&g_peaActiveColor);
		// test eax, eax; je ORIG
		tp[p++] = 0x85; tp[p++] = 0xC0;
		int jeOrig = p; tp[p++] = 0x74; tp[p++] = 0x00;
		// push eax（染色颜色指针，替代原 push 0072289C）
		tp[p++] = 0x50;
		int jbBack = p; tp[p++] = 0xEB; tp[p++] = 0x00;    // jmp BACK
		// ORIG: push 0072289C（原指令）
		int origLabel = p;
		tp[p++] = 0x68; put32(0x72289C);
		// BACK: jmp 0x46E80A（原指令后第一条指令边界）
		int backLabel = p;
		putRelJmp(0x46E80A);

		// 回填 rel8
		fillJ8(jeOrig, origLabel);
		fillJ8(jbBack, backLabel);

		PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);

		int hookOff = tramp - ((int)hookAddr + 5);
		BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
		PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	}
}

// ==================== 卷心菜投手散射（C++ 实现 + 极简 trampoline）====================
// Hook @ 0x464C1C：投掷函数发射点（原代码 mov edx,[edi+1C]; push edx; push edi）
//   trampoline：类型判定 [edi+0x24]==32(Cabbagepult) → call CabbageScatter(edi) → 跳函数末尾
// 散射逻辑全部在 C++（CabbageScatter）里实现：
//   自己遍历本行僵尸按 X 排序取前 N 个（N=等阶：3阶2个 5阶3个），逐个用游戏原生 466E00 发射
//   ——不在游戏索敌函数内部 hook（该处寄存器依赖极脆弱，多次崩溃的根源）
// 发射用 0x466E00（投掷物完整初始化；CreateProjectile 底层创建不显示；Plant::Shoot 内部索敌不可控）
// 标记存 DLL 内存 g_cabbageMarks[僵尸index]，不污染游戏对象
static void CabbageClearMarks()
{
	for (int i = 0; i < 1024; i++)
		g_cabbageMarks[i] = 0;
}

// 游戏原生发射函数: 466E00(植物, 僵尸地址, 行, 变体) → 弹体（stdcall, ret 0x10）
typedef int (__stdcall *FnCabbageShoot)(int plant, int zombie, int row, int variant);
static FnCabbageShoot fnCabbageShoot = (FnCabbageShoot)0x466E00;

static void CabbageScatter(DWORD plantAddr)
{
	int row = MemSafeRead<int>(plantAddr + 0x1C);
	DWORD boardAddr = MemSafeRead<int>(plantAddr + 4);
	if (!boardAddr) return;

	// 收集本行僵尸 (index, X)，按 X 升序（越靠左 = 越靠近植物 = 越靠前）
	PVZ::Board board(boardAddr);
	auto zombies = board.GetAllZombies();
	std::vector<std::pair<int, int>> rowZ;
	for (auto& z : zombies)
	{
		if (z.NotExist) continue;
		if ((int)z.Row != row) continue;
		rowZ.push_back(std::make_pair((int)z.Index, (int)z.X));
	}
	if (rowZ.empty()) return;
	std::sort(rowZ.begin(), rowZ.end(),
		[](const std::pair<int, int>& a, const std::pair<int, int>& b) { return a.second < b.second; });

	// 等阶决定目标数：3阶=2、4阶/5阶=3、以下=1（等同原版单发）
	// （原5阶专属三连散射下调到4阶获得；5阶=3连散射+弹射）
	int exp = 0;
	auto expIt = g_plantExperience.find(plantAddr);
	if (expIt != g_plantExperience.end()) exp = expIt->second;
	int tier = GetPlantTier((int)SeedType::Cabbagepult, exp);
	int maxTargets = (tier >= 4) ? 3 : ((tier == 3) ? 2 : 1);

	// 依次发射（每个目标 1 发）
	int count = 0;
	for (int i = 0; i < (int)rowZ.size() && count < maxTargets; i++)
	{
		int zIdx = rowZ[i].first;
		if (zIdx >= 0 && zIdx < 1024)
			g_cabbageMarks[zIdx] = 1;
		PVZ::Zombie z(zIdx);
		if (z.GetBaseAddress())
			fnCabbageShoot((int)plantAddr, z.GetBaseAddress(), row, 1);
		count++;
	}

	// 冷却补偿（发几颗付几颗的冷却）
	int cd = MemSafeRead<int>(plantAddr + 0x58);
	cd = cd - 180 + count * 60;
	if (cd < 0) cd = 0;
	MemSafeWrite<int>(plantAddr + 0x58, cd);

	// 清标记
	CabbageClearMarks();
}

static void InstallCabbageHooks()
{
	DWORD hookA = 0x464C1C;
	BYTE rawA[5];
	PVZ::Memory::ReadArray<BYTE>(hookA, rawA, 5);
	{
		static const BYTE kExpected[5] = { 0x8B, 0x57, 0x1C, 0x52, 0x57 };
		if (memcmp(rawA, kExpected, 5) != 0)
		{
			CrashStr("HOOKSKIP name=Cabbage site=0x464C1C (bytes changed - modifier?)\r\n");
			return;
		}
	}

	int trampA = (int)TRAMPOLINE_ALLOC();
	if (trampA == 0) return;

	BYTE tp[256];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	// rel32 必须用 DWORD(无符号) 运算：VirtualAlloc 可能返回高地址（int 视为负数）会溢出
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)trampA + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)trampA + (DWORD)p + 4))); };
	auto putNearJcc = [&](int cc) { tp[p++] = 0x0F; tp[p++] = (BYTE)cc; put32(0); };

	// cmp dword [edi+0x24], 32
	tp[p++] = 0x81; tp[p++] = 0x7F; tp[p++] = 0x24; put32(32);
	int jneNotCabbage = p; putNearJcc(0x85); // jne → ORIG
	// 置散射标志（防 onPlantAddProjectile 递归/攻速二次缩放）
	tp[p++] = 0xB8; put32((DWORD)&g_cabbageExtraShooting);
	tp[p++] = 0xC6; tp[p++] = 0x00; tp[p++] = 0x01; // mov byte [eax], 1
	// pushad; push edi; call CabbageScatter; add esp,4; popad
	tp[p++] = 0x60;                                 // pushad
	tp[p++] = 0x57;                                 // push edi
	putRelCall((DWORD)&CabbageScatter);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04; // add esp,4
	tp[p++] = 0x61;                                 // popad
	// 清散射标志
	tp[p++] = 0xB8; put32((DWORD)&g_cabbageExtraShooting);
	tp[p++] = 0xC6; tp[p++] = 0x00; tp[p++] = 0x00; // mov byte [eax], 0
	// 模拟原 0x464C1F/20 的 push（行,植物）保持栈平衡，跳到函数末尾 0x464C34
	tp[p++] = 0x8B; tp[p++] = 0x57; tp[p++] = 0x1C; // mov edx,[edi+0x1C]
	tp[p++] = 0x52; tp[p++] = 0x57;                 // push edx; push edi
	putRelJmp(0x464C34);
	// --- ORIG: 非卷心菜，走原逻辑 ---
	int origPos = p;
	// 回填必须是"偏移-偏移"（rel32 = 目标偏移 - 指令偏移 - 6），绝不能混用绝对地址！
	*(int*)(tp + jneNotCabbage + 2) = origPos - (jneNotCabbage + 6);
	memcpy(tp + p, rawA, 5); p += 5;                // 原5字节
	putRelJmp(0x464C21);                            // 跳回继续原流程

	PVZ::Memory::WriteArray<BYTE>(trampA, tp, p);
	int hookOff = trampA - ((int)hookA + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookA, hook, 5);
}

// ==================== 裂荚射手双向射击（C++ 实现 + 极简 trampoline）====================
// Hook @ 0x464B32：裂荚射击分支入口（原代码 83 F8 1C 75 xx = cmp eax,0x1C; jne）
//   trampoline：类型判定 [edi+0x24]==28(SplitPea) → call SplitPeaShoot(edi) → jmp 0x464B84（裂荚 epilogue）
// 射击逻辑全部在 C++（SplitPeaShoot）里实现：
//   自己遍历本行僵尸判断左右 → 按等阶/状态决定左右各发几颗 → 逐个用游戏原生 0x466E00 发射
//   —— 不在游戏索敌函数内部 hook；发射必须用 0x466E00（CreateProjectile 底层创建不显示）
// 多颗子弹错开：临时改 [植物+0xC]（Y float）发射后恢复（0x466E00 用 [ebp+0xC] 算子弹 Y）
// 方向：variant=1 → [proj+0x58]=6（向左 X-=3.33/帧）；variant=0 → 默认0（向右 X+=3.33/帧）
typedef int (__stdcall *FnSplitShoot)(int plant, int zombie, int row, int variant);
static FnSplitShoot fnSplitShoot = (FnSplitShoot)0x466E00;

// 右键切换裂荚射手状态（5阶）：A↔B + 播放模仿者变身特效（0x47）
// 实现在 UpdateMarigoldFrameInner 右键检测段内统一定位调用
static void SplitPeaCycleForm(DWORD plant, DWORD boardAddr)
{
	(void)boardAddr;
	int& state = g_splitPeaState[plant];
	state = (state == 0) ? 1 : 0;
	// 特效 0x47 = 模仿者变身特效
	__try
	{
		int px = MemSafeRead<int>(plant + 0x8);
		int py = MemSafeRead<int>(plant + 0xC);
		int pw = MemSafeRead<int>(plant + 0x10);
		int ph = MemSafeRead<int>(plant + 0x14);
		if (pw > 0 && pw <= 400 && ph > 0 && ph <= 400)
			Creator::CreateEffect((EffectType::EffectType)0x47, (float)(px + pw / 2), (float)(py + ph / 2));
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

static void SplitPeaShoot(DWORD plantAddr)
{
	// ★★★ 纯 C++ ReadMemory（hook 帧内 __asm 引用局部变量有 MSVC 偏移错位前科，禁用）
	//   ★ 类型必须正确：[plant+8]/[plant+0xC] 是 ImageX/ImageY（int），
	//     按 float 读 = 5.6e-43 垃圾。
	int row = MemSafeRead<int>(plantAddr + 0x1C);
	DWORD boardAddr = MemSafeRead<int>(plantAddr + 4);
	int plantX = MemSafeRead<int>(plantAddr + 8);    // ImageX (int)
	if (!boardAddr) return;

	// 等阶
	int exp = 0;
	auto expIt = g_plantExperience.find(plantAddr);
	if (expIt != g_plantExperience.end()) exp = expIt->second;
	int tier = GetPlantTier((int)SeedType::SplitPea, exp);

	// 5阶状态（0=状态A 左2右3，1=状态B 左3右1；默认 A）
	int state = 0;
	auto stIt = g_splitPeaState.find(plantAddr);
	if (stIt != g_splitPeaState.end()) state = stIt->second;

	// 左右判定：遍历本行僵尸（原生目标槽 [plant+0x98]/[0x9C] 读出是垃圾，弃用）；
	// 僵尸 X 是 float [z+0x2C]，与 int ImageX 比较，±20px 容差分界
	bool hasLeft = false, hasRight = false;
	{
		PVZ::Board board(boardAddr);
		if (board.GetBaseAddress())
		{
			auto zombies = board.GetAllZombies();
			for (auto& z : zombies)
			{
				if (z.NotExist) continue;
				if ((int)z.Row != row) continue;
				float zx = z.X;
				if (zx < (float)(plantX - 20)) hasLeft = true;
				else if (zx > (float)(plantX + 20)) hasRight = true;
			}
		}
	}

	// 数量（按等阶/状态）
	int leftCount = 0, rightCount = 0;
	if (tier >= 5)
	{
		// 5阶：向左触发=任意一侧有僵尸（3阶起向左子弹反弹，可打另一侧）；向右触发=右侧有僵尸
		bool anySide = hasLeft || hasRight;
		leftCount = anySide ? ((state == 0) ? 2 : 3) : 0;
		rightCount = hasRight ? ((state == 0) ? 3 : 1) : 0;
	}
	else if (tier >= 3)
	{
		// 3阶：向左子弹碰屏幕左边反弹 → 左侧或右侧有僵尸都向左2发；右侧有僵尸再向右1发
		leftCount = (hasLeft || hasRight) ? 2 : 0;
		rightCount = hasRight ? 1 : 0;
	}
	else if (tier >= 2)
	{
		// 2阶：左侧有僵尸向左2发；右侧有僵尸向右1发
		leftCount = hasLeft ? 2 : 0;
		rightCount = hasRight ? 1 : 0;
	}
	else
	{
		// 0/1阶：左侧有僵尸向左1发；右侧有僵尸向右1发
		leftCount = hasLeft ? 1 : 0;
		rightCount = hasRight ? 1 : 0;
	}

	if (leftCount == 0 && rightCount == 0)
		return;

	// 攻速：按等阶设置下次攻击间隔（原版 150 厘秒 = 1.5s 基准，与 onPlantAddProjectile 相同公式）
	// currentCD 若为 0（游戏尚未写入），用默认 150 兜底，防止攻击间隔失控
	int newCD = 150;
	float tierSpeed = GetPlantAttackSpeed((int)SeedType::SplitPea, tier);
	if (tierSpeed > 0)
	{
		int currentCD = MemSafeRead<int>(plantAddr + 0x58);
		if (currentCD <= 0) currentCD = 150;
		newCD = (int)(currentCD * tierSpeed / 1.5f);
		if (newCD <= 0) newCD = 1;
	}
	MemSafeWrite<int>(plantAddr + 0x58, newCD);

	// 留声机攻速加成（裂荚冷却基础上再乘）
	{
		float mgf = MgBoostFactor(plantAddr);
		if (mgf < 1.0f)
			MemSafeWrite<int>(plantAddr + 0x58, (int)(newCD * mgf));
	}

	// ★ 双发去重：同一植物 newCD/2 窗口内的第二次调用 = 原版"向后双发"的第二次分支触发，
	//   直接跳过（并补写冷却，防游戏缩短冷却后第三次触发变成真连发）
	{
		int nowTime = MemSafeRead<int>(boardAddr + 0x5568);   // Board+PlayingTime
		int slot = -1;
		for (int i = 0; i < 32; i++)
		{
			if (g_spDedupPlant[i] == plantAddr) { slot = i; break; }
			if (slot < 0 && g_spDedupPlant[i] == 0) slot = i;
		}
		if (slot < 0) slot = 0;
		int gap = nowTime - g_spDedupTime[slot];
		if (g_spDedupPlant[slot] == plantAddr && gap >= 0 && gap < newCD / 2)
		{
			MemSafeWrite<int>(plantAddr + 0x58, newCD);
			return;
		}
		g_spDedupPlant[slot] = plantAddr;
		g_spDedupTime[slot] = nowTime;
	}

	// ★ 连射：当场只发第一颗（先左后右），其余入队由 onGameObjectsUpdate 补发（不堆叠）
	int firstDir = (leftCount > 0) ? 1 : 0;
	g_splitPeaPendingDir = firstDir;
	fnSplitShoot((int)plantAddr, 0, row, firstDir);
	g_splitPeaPendingDir = -1;
	for (int i = 1; i < leftCount; i++)
		SpEnqueue(plantAddr, 1);
	for (int i = (firstDir == 0 ? 1 : 0); i < rightCount; i++)
		SpEnqueue(plantAddr, 0);
}

static void InstallSplitPeaHooks()
{
	DWORD hookA = 0x464B32;
	BYTE rawA[5];
	PVZ::Memory::ReadArray<BYTE>(hookA, rawA, 5);

	// 安全核对：0x464B32 应是以 cmp eax,0x1C 开头的完整指令（83 F8 1C 75 xx）
	// 不符则跳过安装（保持原版行为，绝不崩溃）
	if (rawA[0] != 0x83 || rawA[1] != 0xF8 || rawA[2] != 0x1C || rawA[3] != 0x75)
		return;

	int trampA = (int)TRAMPOLINE_ALLOC();
	if (trampA == 0) return;

	BYTE tp[256];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)trampA + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)trampA + (DWORD)p + 4))); };
	auto putNearJcc = [&](int cc) { tp[p++] = 0x0F; tp[p++] = (BYTE)cc; put32(0); };

	// cmp dword [edi+0x24], 28
	tp[p++] = 0x81; tp[p++] = 0x7F; tp[p++] = 0x24; put32(28);
	int jneNotSplit = p; putNearJcc(0x85); // jne → ORIG
	// pushad; push edi; call SplitPeaShoot; add esp,4; popad
	tp[p++] = 0x60;                                 // pushad
	tp[p++] = 0x57;                                 // push edi
	putRelCall((DWORD)&SplitPeaShoot);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04; // add esp,4
	tp[p++] = 0x61;                                 // popad
	// 跳到裂荚分支 epilogue（pop edi; pop esi; pop ebx; mov esp,ebp; pop ebp; ret），跳过原版双向发射
	putRelJmp(0x464B84);
	// --- ORIG: 非裂荚，走原逻辑 ---
	// ★ 不能复制原 5 字节（83 F8 1C 75 54）：其中 rel8 jne 是相对原地址 0x464B35 编码的，
	//   复制进 trampoline 后偏移错位会跳到垃圾地址。非裂荚直接 jmp 0x464B8B
	//   （原 jne 的目标 = 跳过裂荚分支后的普通射手路径），与原流程语义一致。
	int origPos = p;
	*(int*)(tp + jneNotSplit + 2) = origPos - (jneNotSplit + 6);
	putRelJmp(0x464B8B);

	PVZ::Memory::WriteArray<BYTE>(trampA, tp, p);
	int hookOff = trampA - ((int)hookA + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookA, hook, 5);
}

// ==================== 三线射手等阶机制（v2：零 hook，事件登记 + 轮询处理）====================
// ★ 发射全部走游戏原生 0x466E00(plant, 0, targetRow, 0)（与裂荚同路径，事件 hook 正常登记）
// ★★ 崩溃铁律：事件帧内只做 POD 数组登记 + 纯内存读写 + 只读 map 查找，禁 map 插入/fopen
typedef int (__stdcall *FnTripleShoot)(int plant, int zombie, int row, int variant);
static FnTripleShoot fnTripleShoot = (FnTripleShoot)0x466E00;

// 大招状态登记（POD 数组线性扫描；满 24 株三线同屏属极端场景，返回 nullptr 安全降级）
static TripleState* TripleGetOrCreateState(DWORD plant)
{
	TripleState* free = nullptr;
	for (int i = 0; i < 24; i++)
	{
		if (g_tripleStates[i].plant == plant) return &g_tripleStates[i];
		if (!free && g_tripleStates[i].plant == 0) free = &g_tripleStates[i];
	}
	if (free) { free->plant = plant; free->ultTicks = 0; free->row = 0; return free; }
	return nullptr;
}

// 播放发射音效（游戏原生 0x453630：eax=[0x6A9EC0] app, esi=音效ID；0x1A=发射）
// pushad 包裹防寄存器破坏；hook 帧内调用游戏无副作用函数安全（S4修猫 同款调用）
static void TriplePlayShootSound()
{
	__asm {
		pushad
		mov eax, 0x6A9EC0
		mov eax, [eax]
		mov esi, 0x1A
		mov ebx, 0x453630
		call ebx
		popad
	}
}

// 播放开大音效（游戏原生 0x4560C0：ecx=[0x6A9EC0] app, 栈上音效ID；stdcall ret 4；0x7D=大招）
static void TriplePlayUltSound()
{
	__asm {
		pushad
		mov ecx, 0x6A9EC0
		mov ecx, [ecx]
		push 0x7D
		mov ebx, 0x4560C0
		call ebx
		popad
	}
}

// 三线射手大招齐射（CT 脚本3 同款）：3 颗从植物行原生创建
//   中路直飞 + ±θ 扇形弹（θ=1.14·sin(0.02856·t)，t=大招剩余帧数）
// ★ ±θ 弹速度同步注入：fnTripleShoot 返回后初始化已全部完成，写入即最终态
//   （递归事件经 g_triplePendingDir 登记 proj 地址，此处集中写，写完弹回登记数组）
static void TripleUltShoot(DWORD plant, int row, int tNow)
{
	float theta = TRIPLE_ULT_THA * sinf(TRIPLE_ULT_THW * (float)tNow);
	int n0 = g_triplePendingCount;
	g_triplePendingDir = -1;
	fnTripleShoot((int)plant, 0, row, 0);                  // 中路直飞（原生）
	g_triplePendingDir = TRIPLE_ULT_A;
	fnTripleShoot((int)plant, 0, row, 0);                  // 上偏弹（+θ，递归事件登记）
	g_triplePendingDir = TRIPLE_ULT_B;
	fnTripleShoot((int)plant, 0, row, 0);                  // 下偏弹（−θ，递归事件登记）
	g_triplePendingDir = -1;
	// 同步注入 ±θ 扇形速度（DLL map 标记；[+0x40] 存基准垂直速度供轮询 50 帧翻转）
	for (int i = n0; i < g_triplePendingCount; i++)
	{
		DWORD pr = g_triplePendingMarks[i].proj;
		float vx = TRIPLE_ULT_SPD * cosf(theta);
		float vy = TRIPLE_ULT_SPD * sinf(theta);
		if (g_triplePendingMarks[i].mark == TRIPLE_ULT_B) vy = -vy;
		MemSafeWrite<float>(pr + 0x3C, vx);
		MemSafeWrite<float>(pr + 0x40, vy);
		g_tripleMark[pr] = { g_triplePendingMarks[i].mark, 0.0f, 0 };
	}
	g_triplePendingCount = n0;   // 弹回（±θ 登记已消费；普攻登记不受影响）
}

// 三线射手专用：像素 → 行（Board::PixelToGridY 0x41C550）。
// ★★★ 必须独立成小函数（HypnoPixelToGridX / ExpPouchPixelToGrid 同套路）：
//   onGameObjectsUpdate 巨函数中编译器用 EBX 做帧指针(FPO, C4731)，若 asm 内联在其中
//   且引用局部变量，mov ebx,0x41C550 破坏帧指针后 mov newRow,eax 会把返回值
//   写进 0x41C556 游戏代码段 → 下次执行到该地址即崩溃（实测崩溃地址正是 0x41C556）。
//   独立小函数内编译器走 EBP 正常栈帧，asm 引用局部变量安全。
static int TriplePixelToGridY(int boardAddr, int x, int y)
{
	int row = -1;
	__asm {
		mov ecx, y
		mov edx, boardAddr
		mov eax, x
		mov ebx, 0x41C550
		call ebx
		mov row, eax
	}
	return row;
}

// ★★★ v2 已删除 hook 帧内的 ThreepeaterShootCpp（每帧连发/崩溃根源）：
//   普攻发射完全交还原版，等阶逻辑全部移到 onGameObjectsUpdate 的登记处理块（零 hook）

// ==================== 机枪射手（GatlingPea=40）等阶机制 ====================
static bool UlfTargetable(DWORD zombieAddr, int row);   // 前向声明（实现在大喷菇区块，③ 段命中接管复用）
// 【规格】
//   · 0-2阶：每轮 3 发；3阶：每轮 4 发；4/5阶：每轮 5 发
//   · 5阶：满阶后仍以"未满阶"身份参与经验分配（AddPlantExperience / DistributeRowExperience
//     特判）；超出经验上限（T5阈值=10000）的溢出经验转为大招能量流水——
//     每满 GATLING_ULT_EXP_COST（plant_mechanics.ini，默认 10000）消耗该额度并排队一次大招；
//     短时间溢出 ≥2 次额度 → pending 队列 → 连续释放多次大招。
//   · 大招：向前方 ±15° 锥形匀速喷射豌豆（速率 GATLING_ULT_SPEED，默认 3.33 = 原版豌豆），
//     每颗出生时在 ±15° 内均匀随机方向、初始 Y 在 ±20px 内随机偏移；
//     持续 GATLING_ULT_DURATION_TICKS 共 GATLING_ULT_COUNT（180）颗——v9: 逻辑帧率实测
//     rate≈100 tick/s（GetTickCount 滑动窗口，60 tick 实测仅 0.6 秒），2 秒 = 200 tick，
//     发射改按比例匀速累加器（180/200 ≈ 0.9 颗/tick；旧 perFrame=COUNT/DURATION 在
//     duration=200 时整数除法得 0，一发都打不出）。
//     期间钉住普攻（+0x58=400、+0x90=0），结束写回等阶冷却；pending>0 → 下一帧续开下一轮。
// 【逆向】（dis_plant_region.txt，20260925 纠错★★★）
//   · 机枪分支在 Plant::UpdateShooting 0x464820 内 0x464A2F 处（cmp type,0x28 判定后）：
//     [+0x90]（射击动画倒计时）递减经过 68/51/35/18（0x44/0x33/0x23/0x12）时各发一颗
//     （间隔 17/16/17 tick），命中后 jmp 0x46492C 复用忧郁菇发射块 → call 0x466E00。
//   · ★ 此前 v1/v2 把忧郁菇分支（0x4648C3 cmp eax,0x2a=42 类型判定！触发点 126/98/70/42、
//     枪口闪光 136/108/80/52）误当成机枪 → patch 0x46490C 打错分支 → hookCalls=0。
//   · 另：UpdateShooting 的 this 经 eax 传递（0x463240 call 处 mov eax,plant）， edi=plant。
// 【hook v3】patch 0x464A34 起 30 字节（机枪分支 4 个触发点比较）→ jmp stub
//   （pushad; push edi=Plant*; call GatlingShootCpp cdecl——C 函数按等阶重排触发点
//   {68,51,35,18}（3/4发）+85（5发）并自发射; popad; jmp 0x464934）。
//   首颗（3/4发 cd==68、5发 cd==85）做等阶攻速缩放（与通用攻速块同公式——机枪已从
//   通用块排除，避免一轮 3~5 颗弹逐颗叠乘缩放）。
// 【防普攻】大招起动帧写 [+0x90]=0（UpdateShooting 开头 test 后 je 短路）+ 每帧钉 [+0x58]=400。
// 【大招弹】fnGatlingFire 返回子弹地址（冰西瓜 volley 先例：返回即初始化完成）→ 同步写
//   XSpeed[+0x3C] / YSpeed[+0x40] / 出生Y[+0x34]；g_gatlingUltMark 登记 → 轮询帧每帧
//   TriplePixelToGridY 重算行号（斜飞跨行正确索敌命中）；onProjectileRemove 时 erase。
typedef int (__stdcall *FnGatlingFire)(int plant, int zombie, int row, int variant);
static FnGatlingFire fnGatlingFire = (FnGatlingFire)0x466E00;

// 配置变量 g_gatlingUltExpCost / g_gatlingUltCount / g_gatlingUltDuration /
//   g_gatlingUltSpeed / g_gatlingUltSpreadDeg / g_gatlingUltYRand
//   声明在"机枪射手配置（GATLING_*）"段（LoadPlantMechanicsConfig 之前）。

// ---- 大招状态（POD 定长槽位 + 存活校验；轮询帧专用）----
struct GatlingUltState { DWORD plant; int active; int ultTicks; int fired; int pending; int acc; };
static const int GATLING_ULT_SLOTS = 8;
static GatlingUltState g_gatlingUlt[GATLING_ULT_SLOTS];
// 【v2 已退役】g_gatlingUltEnergy 能量流水：改为"经验扣整万"方案——大招进度直接存在
//   经验值里（UI 显示实际量），死亡时 exp 全额均分给同行，进度随之自动转移。
// 大招弹标记（子弹地址 → 1；轮询帧行号重算名单；onProjectileRemove 时 erase）
static std::map<DWORD, int> g_gatlingUltMark;

// ---- 大招弹 pending 登记（仿三线 g_triplePendingDir / g_triplePendingMarks）----
// 【v2 修复"大招弹统一直飞"】v1 依赖 fnGatlingFire 返回值拿子弹地址，但传 zombie=0 时
//   返回值不可靠（疑似 0）→ if(!proj) 跳过全部速度写入 → 子弹原生直飞。
//   v2 改事件登记：发射前置 g_gatlingPendingUlt=1 → fnGatlingFire 原生创建子弹同步
//   触发 onPlantAddProjectile → 事件内见标记登记 proj 地址 → 发射循环逐颗消费注入
//   ±15° 速度与 ±20px 出生 Y（三线 TripleUltShoot 同款已验证模式）。
static int g_gatlingPendingUlt = 0;                    // 1=当前这颗是大招弹（事件回调消费）
struct GatlingPendingMark { DWORD proj; };
static const int GATLING_PENDING_SLOTS = 16;           // 每帧登记上限（v9 匀速发射后每帧最多约 1~2 颗）
static GatlingPendingMark g_gatlingPendingMarks[GATLING_PENDING_SLOTS];
static int g_gatlingPendingCount = 0;

// ---- hook 安装状态 ----
static int g_gatlingHookState = 0;    // 0未安装 1已安装 -1字节不符 -2trampoline失败
static int g_gatlingInstallTries = 0;

// ---- 逻辑帧节流（v8.1 功能代码，非日志）：事件框架可能同帧双调 GatlingFrame，
//   PlayingTime 未推进即同帧重复 → 跳过全部结算（否则 ultTicks 递减/发弹/驱动全双倍速）。
//   （v9 收工移除机枪诊断日志 D:\pvz_gatling_debug.txt 整套取证，仅保留此节流。）
static int g_gatLastPt = -1;        // 上次有效逻辑帧的 PlayingTime
static int g_gatLastBoard = 0;      // 上次有效逻辑帧的 Board 地址

static GatlingUltState* GatlingUltGetOrCreate(DWORD plant)
{
	GatlingUltState* freeSlot = nullptr;
	for (int i = 0; i < GATLING_ULT_SLOTS; i++)
	{
		if (g_gatlingUlt[i].plant == plant) return &g_gatlingUlt[i];
		if (!freeSlot && g_gatlingUlt[i].plant == 0) freeSlot = &g_gatlingUlt[i];
	}
	if (!freeSlot) return nullptr;   // 槽满（>8 株大招机枪同屏，极端场景）安全降级
	freeSlot->plant = plant;
	freeSlot->active = 0;
	freeSlot->ultTicks = 0;
	freeSlot->fired = 0;
	freeSlot->pending = 0;
	return freeSlot;
}

// 0x464A34 hook 的 C 决策体（cdecl；stub 传入 edi=Plant*）
// ★ 运行在游戏 UpdateShooting 执行流中：只做纯内存读写 + 只读 map 查找（崩溃铁律）
static void __cdecl GatlingShootCpp(DWORD plant)
{
	if (plant < 0x10000) return;
	// patch 点在 UpdateShooting 机枪分支（0x464A2F 已判定 type==0x28）；双保险再读一次类型
	if (MemSafeRead<int>(plant + 0x24) != (int)SeedType::GatlingPea) return;
	int cd = MemSafeRead<int>(plant + 0x90);
	if (cd <= 0) return;

	// 等阶 → 本轮发数（0-2阶3发 / 3阶4发 / 4-5阶5发）
	int exp = 0;
	auto it = g_plantExperience.find(plant);
	if (it != g_plantExperience.end()) exp = it->second;
	int tier = GetPlantTier((int)SeedType::GatlingPea, exp);
	int shots = (tier <= 2) ? 3 : (tier == 3) ? 4 : 5;

	// 发射触发点（20260925 dis 纠错★★★）：机枪分支在 0x464A2F（type==0x28 判定后），
	//   原版 4 连发比较 cmp [+0x90], 0x12(18)/0x23(35)/0x33(51)/0x44(68) —— 递减计数
	//   按 68→51→35→18 顺序经过（间隔 17/16/17）。此前 v1/v2 误把忧郁菇分支（0x4648C3
	//   cmp eax,0x2a=42 类型判定！）的 126/98/70/42 当成机枪触发点 → patch 打错分支
	//   → hookCalls=0（忧郁菇没人种）。
	// 3/4 发取原版 4 点的前 N 个（保留前段节奏）；5 发新增 85（0x55，早于第 1 发 68——
	//   若 +0x90 初值 < 85 则该点永不触发，4/5 阶退化 4 发，lastCd 序列可实测校准）
	static const int firePts4[4] = { 68, 51, 35, 18 };
	static const int fifthPt = 85;
	int fireIdx = -1;
	if (shots >= 5 && cd == fifthPt)
	{
		fireIdx = 0;
	}
	else
	{
		for (int i = 0; i < 4 && i < shots; i++)
		{
			if (cd == firePts4[i]) { fireIdx = i + ((shots >= 5) ? 1 : 0); break; }
		}
	}
	if (fireIdx < 0) return;

	// 本轮首颗：等阶攻速缩放（通用块同公式；首颗触发点天然每轮仅命中一次）
	if (fireIdx == 0)
	{
		float ts = GetPlantAttackSpeed((int)SeedType::GatlingPea, tier);
		if (ts > 0)
		{
			int cur = MemSafeRead<int>(plant + 0x58);
			int newCD = (int)(cur * ts / 1.5f);
			float mgf = MgBoostFactor(plant);
			if (mgf < 1.0f) newCD = (int)(newCD * mgf);
			if (newCD > 0)
				MemSafeWrite<int>(plant + 0x58, newCD);
		}
	}

	int row = MemSafeRead<int>(plant + 0x1C);
	fnGatlingFire((int)plant, 0, row, 0);   // 原生发射（事件 hook 正常走完）
}

// hook 安装：patch 0x464A34（30 字节，机枪分支触发点比较）→ trampoline stub → 跳回 0x464934
static bool InstallGatlingHooks()
{
	// 原字节（dis_plant_region.txt 20260925 纠错核对——机枪分支 0x464A2F 的触发点比较，
	//   patch 点 0x464A34 起 30 字节，已确认无外部跳入）：
	//   mov eax,[edi+0x90]; cmp 0x12/0x23/0x33/0x44 四连比较 je 0x464A52（发射头）;
	//   jne → 0x464934（跳过发射）
	static const BYTE rawG[30] = {
		0x8B, 0x87, 0x90, 0x00, 0x00, 0x00,
		0x83, 0xF8, 0x12, 0x74, 0x13,
		0x83, 0xF8, 0x23, 0x74, 0x0E,
		0x83, 0xF8, 0x33, 0x74, 0x09,
		0x83, 0xF8, 0x44,
		0x0F, 0x85, 0xE2, 0xFE, 0xFF, 0xFF
	};
	DWORD hookA = 0x464A34;
	BYTE cur[30];
	PVZ::Memory::ReadArray<BYTE>(hookA, cur, 30);
	if (memcmp(cur, rawG, 30) != 0)
	{
		g_gatlingHookState = -1;   // 运行时字节不符（版本不匹配 / 已被其他 hook 占用）
		return false;
	}
	int tramp = (int)TRAMPOLINE_ALLOC();
	if (!tramp)
	{
		g_gatlingHookState = -2;
		return false;
	}
	BYTE tp[64];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	// pushad; push edi(Plant*); call GatlingShootCpp(cdecl，C 函数内按等阶自发射);
	//   add esp,4; popad —— 恒跳 0x464934 跳过原版发射块（发射已由 C 函数完成）
	tp[p++] = 0x60;
	tp[p++] = 0x57;
	tp[p++] = 0xE8; put32((int)((DWORD)&GatlingShootCpp - (DWORD)(tramp + p + 4)));
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;
	tp[p++] = 0x61;
	// jmp 0x464934（发射块之后的原生流程：cmp [+0x90],0 → 收招判定）
	tp[p++] = 0xE9; put32((int)(0x464934 - (DWORD)(tramp + p + 4)));

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int off = tramp - ((int)hookA + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &off, 4);
	PVZ::Memory::WriteArray<BYTE>(hookA, hook, 5);
	g_gatlingHookState = 1;
	return true;
}

// ---- v9 大招弹命中特效（接管命中弹"凭空消失"补视觉）----
// 普通豌豆（Type=0）：粒子 0x25"豌豆：破裂"（数值表），走 SeaBurstSpawnParticle
//   （0x453C80 现成封装，海蘑菇毒爆实测可用；renderOrder 0x61A80 通用）。
// 火豌豆（Type=6，过火炬/炎豌豆同款）：reanim 0x22"火豆命中火焰"，管道照抄
//   FireBallHitEffect / DoomPurpleBurnFx（2026-09-13 槽位修正定案：[esp]=X、[esp+4]=Y），
//   原版橙焰不染色；子弹坐标系修正 X+[0x67A288]、Y-[0x679338]（与火豆命中管道同源）。
// ★ 铁律：float 不跨 __asm——视觉坐标以 DWORD 位模式经静态变量传入。
static DWORD SeaBurstSpawnParticle(float x, float y, int effectId);   // 实体在 SeaShroom 区

static DWORD g_gatFxApp = 0;
static DWORD g_gatFxLayer = 0;
static DWORD g_gatFxXBits = 0;
static DWORD g_gatFxYBits = 0;

static void GatlingUltFireFx(DWORD lawnApp, float visX, float visY, DWORD layer)
{
	if (!lawnApp) return;
	g_gatFxApp = lawnApp;
	g_gatFxLayer = layer;
	g_gatFxXBits = *(DWORD*)&visX;
	g_gatFxYBits = *(DWORD*)&visY;
	__try
	{
	__asm
	{
		pushad
		mov eax, g_gatFxApp
		mov ebx, 0x22                    // reanim 0x22 = 火豆命中火焰（原版 0x46E25F 段）
		mov ecx, g_gatFxLayer
		push ecx
		sub esp, 8
		; [esp]=X、[esp+4]=Y（引擎真实参数序，2026-09-13 槽位修正）
		mov edx, offset g_gatFxXBits
		fld dword ptr [edx]
		mov edx, 0x67A288
		fadd qword ptr [edx]             ; X + 原版子弹系修正
		fstp dword ptr [esp]
		mov edx, offset g_gatFxYBits
		fld dword ptr [edx]
		mov edx, 0x679338
		fsub qword ptr [edx]             ; Y - 原版子弹系修正
		fstp dword ptr [esp + 4]
		mov edx, 0x453C30
		call edx                         // eax = Animation*（stdcall ret 0xC 自清 3 参数）
		test eax, eax
		je gffx_done                     // 创建失败直接退（防空指针写崩）
		mov edi, eax                     // 原版字段初始化（0x46E298-0x46E2B9）
		mov edx, 0x67952C
		fld dword ptr [edx]
		fstp dword ptr [edi + 4]
		mov edx, 0x679638
		fld dword ptr [edx]
		fstp dword ptr [edi + 8]
		mov edx, 0x679928
		fld dword ptr [edx]
		fstp dword ptr [edi + 0x24]
		mov edx, 0x664A5C
		fld dword ptr [edx]
		fstp dword ptr [edi + 0x34]
	gffx_done:
		popad
	}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 每帧轮询（onGameObjectsUpdate 调用）：经验溢出→大招排队 + 大招状态机 + 大招弹行号重算
static void GatlingFrame(int boardAddress)
{
	// hook 延迟安装（重试 240 帧；字节不符 -1 时停止重试——版本不匹配重试无用）
	if (g_gatlingHookState == 0 || g_gatlingHookState == -2)
	{
		if (g_gatlingInstallTries < 240)
		{
			g_gatlingInstallTries++;
			InstallGatlingHooks();
		}
	}
	// v8.1 逻辑帧节流：PlayingTime 未推进（同帧重复调用/暂停）→ 跳过全部结算，
	// 否则 ultTicks 递减/发弹/驱动全双倍速（曾实锤"60 tick 仅 1 秒"）。
	// ★ boardAddress 参数即 Board（调用处已验证 GetBaseAddress()），直接 +0x5568 读 PlayingTime——
	//   v6 曾错误地把 0x5568 加在 LawnApp 指针上（越界读 → 每帧异常被 __except 吞 →
	//   GatlingFrame 全链死 → 只攒经验不开大）。
	int ptNow = boardAddress ? MemSafeRead<int>(boardAddress + 0x5568) : -1;
	if (ptNow == g_gatLastPt && boardAddress == g_gatLastBoard)
		return;
	g_gatLastPt = ptNow;
	g_gatLastBoard = boardAddress;

	PVZ::Board board(boardAddress);
	if (!board.GetBaseAddress()) return;

	// ---- ① 经验溢出 → 大招排队（v2 扣整万，不钳制）----
	// 机枪经验吸收不设上限（AddPlantExperience 特判）：超过 T5 阈值（limit）后每满
	// 一次 EXP_COST 从经验中扣除并排队一次大招——经验值 UI 显示实际量（在
	// [limit, limit+EXP_COST) 区间波动，开大瞬间回落 limit），等阶恒 5 不受影响
	// （GetPlantTier 判 5 阶只看 exp >= limit，扣整万后仍 >= limit）。
	// 死亡时 exp 全额均分给同行（onPlantRemove 既有路径），大招进度随之自动转移。
	int limit = GetSeedExperienceLimit((int)SeedType::GatlingPea);
	auto plants = board.GetAllPlants();
	for (auto& plant : plants)
	{
		if (plant.Type != SeedType::GatlingPea) continue;
		if (plant.NotExist) continue;
		DWORD addr = plant.GetBaseAddress();
		if (!addr) continue;
		auto it = g_plantExperience.find(addr);
		if (it == g_plantExperience.end()) continue;
		if (it->second < limit) continue;
		while (it->second - limit >= g_gatlingUltExpCost)
		{
			it->second -= g_gatlingUltExpCost;    // 扣整万（UI 显示实际经验量）
			GatlingUltState* st = GatlingUltGetOrCreate(addr);
			if (st) st->pending++;                // 短时间多次额度 → 连续多次大招
		}
	}

	// ---- ② 大招状态机 ----
	float spreadRad = g_gatlingUltSpreadDeg * 3.14159265f / 180.0f;
	for (int i = 0; i < GATLING_ULT_SLOTS; i++)
	{
		GatlingUltState& st = g_gatlingUlt[i];
		if (st.plant == 0) continue;
		DWORD pa = st.plant;
		// 失效清理（铲除/死亡/内存池复用；pending 大招随之丢弃）
		if (!MemSafeRead<int>(pa) ||
			MemSafeRead<BYTE>(pa + 0x141) ||
			MemSafeRead<int>(pa + 0x24) != (int)SeedType::GatlingPea)
		{
			st.plant = 0; st.active = 0; st.pending = 0; st.fired = 0; st.ultTicks = 0; st.acc = 0;
			continue;
		}

		if (!st.active)
		{
			if (st.pending > 0)
			{
				st.pending--;
				st.active = 1;
				st.ultTicks = g_gatlingUltDuration;
				st.fired = 0;
				st.acc = 0;   // v9 匀速累加器清零
				// 中断普攻射击动画（+0x90=0 → UpdateShooting 开头 test 后 je 短路）
				MemSafeWrite<int>(pa + 0x90, 0);
			}
			continue;
		}

		// v9 按时长比例匀速发射：每 tick 累加 COUNT，攒满 DURATION 发一颗（180/200 ≈ 0.9
		//   颗/tick，200 tick 发完 180 颗）。旧 perFrame=COUNT/DURATION 是"每帧固定颗数"，
		//   duration 从 60 改 200 后整数除法得 0（if(perFrame<1) 强抬 1 → 会提前 60 颗打完）。
		st.acc += g_gatlingUltCount;
		int toFire = (g_gatlingUltDuration > 0) ? st.acc / g_gatlingUltDuration : 1;
		st.acc -= toFire * g_gatlingUltDuration;
		if (st.fired + toFire > g_gatlingUltCount) toFire = g_gatlingUltCount - st.fired;
		int row = MemSafeRead<int>(pa + 0x1C);
		for (int k = 0; k < toFire; k++)
		{
			st.fired++;
			// ±15° 内连续均匀随机方向
			float ang = (((rand() % 2001) - 1000) / 1000.0f) * spreadRad;
			// 【v2】事件登记拿弹地址（不依赖 fnGatlingFire 返回值——传 zombie=0 时返回值
			//   不可靠，v1 因此全部写入被跳过 → 大招弹统一直飞）：
			//   置标记 → 原生发射（同步触发 onPlantAddProjectile 登记 proj 地址）→ 消费注入
			int before = g_gatlingPendingCount;
			g_gatlingPendingUlt = 1;
			fnGatlingFire((int)pa, 0, row, 0);
			g_gatlingPendingUlt = 0;   // 兜底清（事件未触发时不得影响下一颗）
			for (int i = before; i < g_gatlingPendingCount && i < GATLING_PENDING_SLOTS; i++)
			{
				DWORD pr = g_gatlingPendingMarks[i].proj;
				if (!pr) continue;
				// 【v8】同步注入：出生视觉偏移走 Height（渲染位置 = Y − Height）——
				//   Y 完全不动：①绕开原版"弹落地面"判定（向下弹撞弹道下界即播命中特效
				//   消失，实测"打到地上"）；②保住火炬过火判定（按弹道 y，v7 实测 y 被改
				//   后火豌豆失效）。height 减小 = 视觉下移。
				int dy = (rand() % (2 * g_gatlingUltYRand + 1)) - g_gatlingUltYRand;
				float h0 = MemSafeRead<float>(pr + 0x38);
				MemSafeWrite<float>(pr + 0x38, h0 - (float)dy);
				float vx = g_gatlingUltSpeed * cosf(ang);   // XSpeed
				float vy = g_gatlingUltSpeed * sinf(ang);   // YSpeed（仅作自驱动存储，原生不消费）
				MemSafeWrite<float>(pr + 0x3C, vx);
				MemSafeWrite<float>(pr + 0x40, vy);
				g_gatlingUltMark[pr] = 1;
			}
			g_gatlingPendingCount = before;   // 弹回（登记已消费）
		}

		// 钉住普攻（冷却 400 + 射击动画清零）——大招期间不普攻
		MemSafeWrite<int>(pa + 0x58, 400);
		if (MemSafeRead<int>(pa + 0x90) != 0)
			MemSafeWrite<int>(pa + 0x90, 0);

		st.ultTicks--;
		if (st.fired >= g_gatlingUltCount || st.ultTicks <= 0)
		{
			st.active = 0;
			// 结束写回等阶冷却（三线同款公式：150 基准 × 等阶攻速 / 1.5）
			int exp2 = 0;
			auto eIt2 = g_plantExperience.find(pa);
			if (eIt2 != g_plantExperience.end()) exp2 = eIt2->second;
			int tier2 = GetPlantTier((int)SeedType::GatlingPea, exp2);
			float ts2 = GetPlantAttackSpeed((int)SeedType::GatlingPea, tier2);
			int cd2 = 150;
			if (ts2 > 0) cd2 = (int)(150 * ts2 / 1.5f);
			float mgf = MgBoostFactor(pa);
			if (mgf < 1.0f) cd2 = (int)(cd2 * mgf);
			if (cd2 <= 0) cd2 = 1;
			MemSafeWrite<int>(pa + 0x58, cd2);
			// pending>0 → 下一帧 !active 分支立即续开下一轮（连续大招）
		}
	}

	// ---- ③ 大招弹驱动 + 行号重算 ----
	// ★★★ v8 机制定案：原生直飞弹不消费 [+0x40] YSpeed（v4/v5 A/B 实锤），散开 =
	//   本轮询逐帧驱动。v7 实测驱动 Y（+0x34）的两个副作用：①向下弹触发原版"弹落
	//   地面"判定（弹道下界播命中特效销毁）→"向下没有倾角"；②弹道 y 被改 → 火炬
	//   过火判定失效 → 火豌豆消失。**v8 散开改走 Height(+0x38)**：渲染位置=Y−Height，
	//   y 恒定 → 打地判定/火炬判定全部恢复，视觉散开不变（height 减小=视觉下移）。
	auto projectiles = board.GetAllProjectile();
	for (auto& proj : projectiles)
	{
		if (proj.NotExist) continue;
		int pAddr = proj.GetBaseAddress();
		if (!pAddr) continue;
		if (g_gatlingUltMark.find(pAddr) == g_gatlingUltMark.end()) continue;
		// Height 自驱动（±15° 散开的唯一动力源）：vy>0 向下 → height 减小 → 视觉下移
		float hCur = MemSafeRead<float>(pAddr + 0x38);
		float vy = MemSafeRead<float>(pAddr + 0x40);
		MemSafeWrite<float>(pAddr + 0x38, hCur - vy);
		// 行号重算改用视觉位置（Y − Height）：跨行命中跟随视觉行
		float visY = proj.Y - hCur;
		int newRow = TriplePixelToGridY(boardAddress, (int)proj.X, (int)(visY + 40.0f));
		if (newRow >= 0 && newRow <= 5)
			MemSafeWrite<int>(pAddr + 0x1C, newRow);
		// ★ v8.2 命中接管：原版命中判定只读弹道 y（不认 Height 视觉偏移），Height 散开的
		//   弹会从其他路僵尸身上飞过（v8 实测）。大招弹命中由本轮询接管：
		//   视觉行 + x 重叠 → PVZ::Zombie::Hit（原版 TakeDamage 流程：防具/死亡/掉头全兼容）
		//   → 移除弹（豌豆不穿透）。v9 已补命中特效（普通豌豆 0x25 粒子 / 火豌豆 0x22 橙焰）。
		if (newRow >= 0 && newRow <= 5)
		{
			int px = (int)proj.X;
			DWORD hitZ = 0;
			int hitZx = 0x7FFFFFFF;
			auto zombies = board.GetAllZombies();
			for (auto& z : zombies)
			{
				if (z.NotExist) continue;
				DWORD zAddr = z.GetBaseAddress();
				if (!zAddr || !UlfTargetable(zAddr, newRow)) continue;
				// ★ Zombie::X=+0x2C 是 FLOAT（PVZ.h）——v8.2 误按 int 读（float 位模式=11 亿）
				//   → x 窗口判定永远为假 → hits=0。改读 float。
				int zx = (int)MemSafeRead<float>(zAddr + 0x2C);
				if (px >= zx - 10 && px <= zx + 45 && zx < hitZx)
				{
					hitZx = zx;
					hitZ = zAddr;
				}
			}
			if (hitZ)
			{
				PVZ::Zombie zb(hitZ);
				zb.Hit(20);   // 原版豌豆伤害（flags=DAMAGEF_NONE，正常防具结算）
				// v9 命中特效：普通豌豆=粒子 0x25"豌豆破裂"；火豌豆（过火炬后 Type=6）=
				//   reanim 0x22 橙焰（与炎豌豆同款）。坐标用视觉位置（Y−Height），
				//   reanim 层 = 弹 renderOrder(+0x20)+1（FireBallHitEffect 同款）。
				{
					int ptype = MemSafeRead<int>(pAddr + 0x5C);
					DWORD fxApp = MemSafeRead<DWORD>(pAddr);
					if (ptype == 6)
					{
						GatlingUltFireFx(fxApp, (float)proj.X, visY,
							MemSafeRead<DWORD>(pAddr + 0x20) + 1);
					}
					else
					{
						SeaBurstSpawnParticle((float)proj.X, visY, 0x25);
					}
				}
				MemSafeWrite<BYTE>(pAddr + 0x50, 1);   // NotExist=1 移除弹
				g_gatlingUltMark.erase(pAddr);
			}
		}
	}
}

// ★★★ v2 已删除 InstallThreepeaterHooks（0x464A8F hook 弃用，零 hook 方案）

// ===== 三叶草等阶效果触发（吹飞时刻 hook → onGameObjectsUpdate 延迟执行）=====
// hook @ 0x460F4B（Blover Update 中 call 0x4666A0 处）只记录三叶草地址，
// 实际触发在 onGameObjectsUpdate（先分配挂起的死亡经验，保证读到正确等阶）。
// 原版吹飞飞行僵尸（0阶，不干预）；等阶效果叠加：1阶全屏减速 / 2阶全屏击退 / 3阶攻速增益。

// 吹飞时刻记录三叶草（不立即执行——铲同行植物转移的经验要等分配完成，见 onGameObjectsUpdate）
void RecordBloverTrigger(DWORD plantAddr)
{
	if (plantAddr == 0) return;
	g_pendingBloverTriggers.insert((int)plantAddr);
}

void TriggerBloverEffects(DWORD plantAddr)
{
	if (plantAddr == 0) return;
	int rawType = MemSafeRead<int>(plantAddr + 0x24);
	if (rawType != (int)SeedType::Blover) return;

	int exp = 0;
	auto expIt = g_plantExperience.find(plantAddr);
	if (expIt != g_plantExperience.end())
		exp = expIt->second;
	int tier = GetPlantTier(rawType, exp);
	if (tier < 1)
		return;

	int pvzBase = MemSafeRead<int>(0x6A9EC0);
	if (pvzBase < 0x400000) return;
	int boardAddr = MemSafeRead<int>(pvzBase + 0x768);
	if (!boardAddr) return;
	PVZ::Board board(boardAddr);
	int nowTime = board.PlayingTime;
	auto zombies = board.GetAllZombies();

	// 1阶: 全屏僵尸减速10s（原版吹飞尚未执行，飞行僵尸也减速，随即被吹飞无副作用）
	for (auto& zombie : zombies)
	{
		if (!zombie.isValid() || zombie.NotExist) continue;
		zombie.Decelerate(1000); // 10秒 = 1000厘秒
	}

	// 2阶: 全屏击退（向后退 = X 增大）
	if (tier >= 2)
	{
		for (auto& zombie : zombies)
		{
			if (!zombie.isValid() || zombie.NotExist) continue;
			float newX = zombie.X + (float)g_bloverKnockbackDistance;
			if (newX < 0.0f) newX = 0.0f;
			zombie.X = newX;
		}
	}

	// 3阶: 全屏植物攻速提升（仅记录结束时刻，实际缩减在 onPlantAddProjectile / onDrawExpUI 应用）
	// 多次触发取较晚结束时刻(延长增益)，不叠加缩减比例
	if (tier >= 3)
	{
		int endTime = nowTime + g_bloverSpeedBoostDuration;
		if (endTime > g_bloverBoostEndTime)
			g_bloverBoostEndTime = endTime;
	}
}

// 三叶草"开始吹"时刻 hook：
// 三叶草生效的真实路径在植物 Update 主函数末尾的通用生效逻辑（对灰烬植物通用）：
//   0x4633FB: mov eax,[edi+0x50]     ; EffectiveCountdown 生效倒计时
//   0x4633FE: test eax,eax
//   0x463400: jle 0x463410
//   0x463402: add eax,-1             ; 每帧递减
//   0x463405: mov [edi+0x50],eax
//   0x463408: jne 0x463410           ; 未归零跳过
//   0x46340A: push edi               ; [esp]=plant
//   0x46340B: call 0x4666A0          ; ★ hook 此处(5字节 E8 90 32 00 00) = 生效/吹飞
//   0x463410: pop edi; pop esi; pop ecx; ret
// 注意：Blover Update(0x460F00) 内的 0x460F4B call 0x4666A0 分支因生效后
// State 已=2 而永不执行（0x460F42 je 跳过），不是三叶草的真实生效路径。
// trampoline: 判定 [esp](=plant) 类型==27(Blover) → 记录延迟触发 → call 0x4666A0(原生效) → jmp 0x463410
static void InstallBloverHook()
{
	DWORD hookAddr = 0x46340B;
	BYTE rawA[5];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, rawA, 5);
	{
		static const BYTE kExpected[5] = { 0xE8, 0x90, 0x32, 0x00, 0x00 };
		if (memcmp(rawA, kExpected, 5) != 0)
		{
			CrashStr("HOOKSKIP name=Blover site=0x46340B (bytes changed - modifier?)\r\n");
			return;
		}
	}

	int trampA = (int)TRAMPOLINE_ALLOC();
	if (trampA == 0) return;

	BYTE tp[64];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	// rel32 必须用 DWORD(无符号) 运算：VirtualAlloc 可能返回高地址（int 视为负数）会溢出
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)trampA + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)trampA + (DWORD)p + 4))); };

	// 进入时 [esp] = plant（0x46340A push edi 压入，植物 Update 主函数上下文，必为有效植物）
	tp[p++] = 0x8B; tp[p++] = 0x04; tp[p++] = 0x24;          // mov eax,[esp]
	tp[p++] = 0x83; tp[p++] = 0x78; tp[p++] = 0x24; tp[p++] = 0x1B; // cmp dword ptr [eax+0x24], 0x1B
	int jneNotBlover = p;
	tp[p++] = 0x75; tp[p++] = 0x00;                          // jne ORIG (回填)
	tp[p++] = 0x60;                                          // pushad
	// PUSHAD 压 32 字节：原 [esp]（plant）位于 [esp+0x20]
	// push [esp+0x20] 编码 = FF 74 24 20（modrm 74=mod01/reg6/push/rm=SIB; SIB 24=无index+base=ESP; disp8=20）
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x20; // push dword ptr [esp+0x20]  (plant)
	putRelCall((DWORD)&RecordBloverTrigger);                 // 只记录，延迟到 onGameObjectsUpdate 触发
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;          // add esp,4
	tp[p++] = 0x61;                                          // popad
	// ORIG: 非三叶草（或其他灰烬植物）直接走原生效逻辑
	*(BYTE*)(tp + jneNotBlover + 1) = (BYTE)(p - (jneNotBlover + 2)); // 回填 jne rel8
	// 还原原 call 0x4666A0 语义：执行原生效/吹飞逻辑（ret 4 清 plant 后返回 trampoline）
	putRelCall(0x4666A0);
	putRelJmp(0x463410);                                     // 返回植物 Update 主函数末尾

	PVZ::Memory::WriteArray<BYTE>(trampA, tp, p);
	int hookOff = trampA - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
}

// ==================== 植物阳光/冷却外部配置 + 获得关卡外部配置 ====================
// 【阳光/冷却】数据源 = PlantDefinition 静态表：
//   基址 0x69F2B0 + 0x24*SeedType，字段偏移：
//     +0x10 Cost(阳光)   +0x14 Cooldown(厘秒,750=7.5秒)   +0x1C AttackCooldown(厘秒)
//   游戏所有价格显示/扣费/冷却都读这张表 → 直接写表即生效（重新进关刷新）。
// 【获得关卡】掉落逻辑 = GetAwardSeedForLevel @ 0x453A90：
//   eax = 1基关卡号(1-1=1 ... 5-10=50) → 返回 eax = 掉落 SeedType(0~40)。
//   该函数是纯算术映射（无静态表可改）→ 用 trampoline hook 覆盖返回值，
//   配置未命中时执行复制进 trampoline 的原版算术（保持原行为）。
// 配置文件：plant_cost.ini / plant_unlock.ini（UTF-8 注释、';' 行注释）
#define PLANTDEF_TABLE      0x69F2B0
#define PLANTDEF_STRIDE     0x24
#define PLANTDEF_OFF_COST   0x10
#define PLANTDEF_OFF_CD     0x14

static bool g_awardSeedHookInstalled = false;
static int g_unlockOverride[50];   // 0基索引(关卡号-1) → 掉落SeedType；-1 = 未配置走原版
static int g_unlockLevel[53];      // 植物 → 解锁关卡（1基）；-1 = 未配置走原版
static bool g_unlockHookInstalled = false;

// 诊断日志（仅限 init() 等安全上下文调用，禁止在 hook/事件回调帧内调用——见崩溃铁律）
static void PlantCfgLog(const char* fmt, ...)
{
	FILE* f = fopen("D:\\pvz_plantcfg_debug.log", "a");
	if (!f)
		return;
	va_list ap;
	va_start(ap, fmt);
	vfprintf(f, fmt, ap);
	va_end(ap);
	fclose(f);
}

// 打开配置文件：优先 CWD，其次 DLL 所在目录（= 游戏目录，防快捷方式启动导致 CWD 不对）
static std::ifstream OpenConfigFile(const char* name)
{
	std::ifstream f(name);
	if (f.is_open())
	{
		PlantCfgLog("[cfg] opened '%s' from CWD\n", name);
		return f;
	}
	char dllPath[MAX_PATH] = { 0 };
	HMODULE hMod = NULL;
	GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
		(LPCSTR)&OpenConfigFile, &hMod);
	GetModuleFileNameA(hMod, dllPath, MAX_PATH);
	std::string dir = dllPath;
	size_t pos = dir.find_last_of('\\');
	if (pos != std::string::npos)
		dir = dir.substr(0, pos);
	PlantCfgLog("[cfg] CWD open failed, trying DLL dir: %s\n", dir.c_str());
	std::ifstream f2((dir + "\\" + name).c_str());
	if (f2.is_open())
		PlantCfgLog("[cfg] opened '%s' from DLL dir\n", name);
	return f2;
}

// 解析 "x-y"（1基关卡）→ 1..50 关卡号；失败返回 0
static int ParseLevelString(const std::string& s)
{
	int big = 0, small = 0;
	char c;
	std::istringstream iss(s);
	iss >> big >> c >> small;
	if (big >= 1 && big <= 5 && small >= 1 && small <= 10)
		return (big - 1) * 10 + small;
	return 0;
}

// 加载 plant_cost.ini：SeedType = Cost, Cooldown（不写攻速字段！攻速由等阶系统独立管理）
void LoadPlantCostConfig()
{
	PlantCfgLog("[plant_cost] ===== LoadPlantCostConfig begin =====\n");
	char cwd[MAX_PATH] = { 0 };
	GetCurrentDirectoryA(MAX_PATH, cwd);
	PlantCfgLog("[plant_cost] CWD: %s\n", cwd);

	std::ifstream file = OpenConfigFile("plant_cost.ini");
	if (!file.is_open())
	{
		PlantCfgLog("[plant_cost] !! plant_cost.ini open FAILED\n");
		return;
	}
	PlantCfgLog("[plant_cost] plant_cost.ini opened OK\n");

	std::string line;
	int okCount = 0;
	while (std::getline(file, line))
	{
		if (line.empty() || line[0] == ';' || line[0] == '#')
			continue;
		size_t eqPos = line.find('=');
		if (eqPos == std::string::npos)
			continue;

		int seedType = std::atoi(line.substr(0, eqPos).c_str());
		if (seedType < 0 || seedType > 52)
			continue;

		std::string val = line.substr(eqPos + 1);
		size_t sc = val.find(';');
		if (sc != std::string::npos)
			val = val.substr(0, sc);

		// 拆逗号分隔字段（最多 3 个，忽略第 3 个攻速字段）
		int fields[3] = { -1, -1, -1 };
		int cnt = 0;
		size_t pos = 0;
		while (cnt < 3)
		{
			size_t comma = val.find(',', pos);
			std::string part;
			if (comma == std::string::npos)
			{
				part = val.substr(pos);
				fields[cnt++] = std::atoi(part.c_str());
				break;
			}
			part = val.substr(pos, comma - pos);
			fields[cnt++] = std::atoi(part.c_str());
			pos = comma + 1;
		}
		if (cnt < 2)
			continue;

		DWORD base = PLANTDEF_TABLE + PLANTDEF_STRIDE * seedType;
		if (fields[0] >= 0)
			MemSafeWrite<int>(base + PLANTDEF_OFF_COST, fields[0]);
		if (fields[1] >= 0)
			MemSafeWrite<int>(base + PLANTDEF_OFF_CD, fields[1]);
		// 注意：不再写 +0x1C（AttackCooldown），攻速完全交给等阶系统
		okCount++;
		PlantCfgLog("[plant_cost] type=%d cost=%d cd=%d\n", seedType, fields[0], fields[1]);
	}
	file.close();
	PlantCfgLog("[plant_cost] applied %d entries\n", okCount);
}

// 加载 plant_unlock.ini：SeedType = x-y（1基关卡）
void LoadPlantUnlockConfig()
{
	PlantCfgLog("[unlock] ===== LoadPlantUnlockConfig begin =====\n");
	for (int i = 0; i < 50; i++)
		g_unlockOverride[i] = -1;
	for (int i = 0; i < 53; i++)
		g_unlockLevel[i] = -1;

	std::ifstream file = OpenConfigFile("plant_unlock.ini");
	if (!file.is_open())
	{
		PlantCfgLog("[unlock] !! plant_unlock.ini open FAILED\n");
		return;
	}
	PlantCfgLog("[unlock] plant_unlock.ini opened OK\n");

	std::string line;
	int okCount = 0;
	while (std::getline(file, line))
	{
		if (line.empty() || line[0] == ';' || line[0] == '#')
			continue;
		size_t eqPos = line.find('=');
		if (eqPos == std::string::npos)
			continue;

		int seedType = std::atoi(line.substr(0, eqPos).c_str());
		// ★ 2026-10-03 越界修复：g_unlockLevel 只有 53 项（下标 0..52），
		//   原判断 `> 53` 会放行 seedType==53 → g_unlockLevel[53] 越界写 4 字节，
		//   砸到紧随其后的全局 g_kbPowFxQCount（map 反查实证：
		//   g_unlockLevel@0x1005B140 + 53*4 = 0x1005B214 = g_kbPowFxQCount）
		//   → 队列计数被写成关卡号，后续 g_kbPowFxQ[count++] 连环越界。
		//   读取侧 MyIsUnlocked 用的是 `< 53`，此处与之对齐。
		if (seedType < 0 || seedType >= 53)
			continue;

		std::string val = line.substr(eqPos + 1);
		size_t sc = val.find(';');
		if (sc != std::string::npos)
			val = val.substr(0, sc);

		int level = ParseLevelString(val);
		if (level >= 1 && level <= 50)
		{
			g_unlockOverride[level - 1] = seedType;   // 掉落 hook：关卡 → 植物
			g_unlockLevel[seedType] = level;          // 解锁 hook：植物 → 关卡（1基）
			okCount++;
			PlantCfgLog("[unlock] level=%d -> seed=%d\n", level, seedType);
		}
	}
	file.close();
	PlantCfgLog("[unlock] applied %d entries\n", okCount);
}

// GetAwardSeedForLevel hook 回调：命中配置返回掉落植物；未命中返回 -1（走原版算术）
// 纯数组查询，无 CRT/容器，hook 上下文安全
static int __cdecl GetAwardSeedOverride(int level)
{
	if (level >= 1 && level <= 50)
	{
		int v = g_unlockOverride[level - 1];
		if (v >= 0)
			return v;
	}
	return -1;
}

// 安装 0x453A90 hook（GetAwardSeedForLevel）
// 调用约定（反汇编确认）：eax = 1基关卡号 → 返回 eax = 掉落 SeedType，无栈参数
// trampoline 布局：
//   [0x00] PUSHAD / mov ebx,eax / push eax / call GetAwardSeedOverride / add esp,4
//   [0x0C] test eax,eax; js +8 → fallback（-1 未命中）
//   [0x10] mov [esp+0x1C],eax(写回EAX槽); POPAD; ret          ← 配置命中直接返回
//   [0x18] fallback: lea eax,[ebx-1]; <复制原版算术 453A93..453ABC(0x2A字节)>
//   [0x45] mov [esp+0x1C],eax; POPAD; ret                    ← 原版 ret 被替换为写回+返回
// ★ 复制区内部 rel8 跳转相对位置不变，无需修正；末尾 jle(7E 05) 恰好跳到追加区开头。
void InstallAwardSeedHook()
{
	DWORD hookAddr = 0x453A90;

	// 修改器共存：站点已被改写（PVZTools 等先装了 hook）→ 跳过安装，防 trampoline
	// 拷贝到被改字节后 rel32/指令边界失配跳飞
	{
		BYTE cur[5];
		PVZ::Memory::ReadArray<BYTE>(hookAddr, cur, 5);
		static const BYTE kExpected[5] = { 0x83, 0xC0, 0xFF, 0x99, 0xB9 };
		if (memcmp(cur, kExpected, 5) != 0)
		{
			CrashStr("HOOKSKIP name=AwardSeed site=0x453A90 (bytes changed - modifier?)\r\n");
			return;
		}
	}

	// 原版算术部分：453A93(cdq) ~ 453ABC(mov eax,0x28 末字节)，不含 453ABD 的 ret
	BYTE orig[0x2A];
	PVZ::Memory::ReadArray<BYTE>(hookAddr + 3, orig, sizeof(orig));

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return;

	BYTE tp[160];
	int p = 0;
	tp[p++] = 0x60;                                  // PUSHAD
	tp[p++] = 0x89; tp[p++] = 0xC3;                  // mov ebx, eax（备份关卡号）
	tp[p++] = 0x50;                                  // push eax（handler 参数）
	int callOff = (int)&GetAwardSeedOverride - (tramp + p + 5);
	tp[p++] = 0xE8; memcpy(tp + p, &callOff, 4); p += 4;   // call GetAwardSeedOverride
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;  // add esp, 4
	tp[p++] = 0x85; tp[p++] = 0xC0;                  // test eax, eax
	tp[p++] = 0x78; tp[p++] = 0x08;                  // js +8 → fallback
	tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x1C; // mov [esp+0x1C], eax
	tp[p++] = 0x61;                                  // POPAD
	tp[p++] = 0xC3;                                  // ret
	tp[p++] = 0x90; tp[p++] = 0x90;                  // nop nop（fallback 对齐 @0x18）
	tp[p++] = 0x8D; tp[p++] = 0x43; tp[p++] = 0xFF;  // lea eax, [ebx-1]（= 原 add eax,-1）
	memcpy(tp + p, orig, sizeof(orig)); p += sizeof(orig); // 原版算术（cdq..mov eax,0x28）
	tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x1C; // mov [esp+0x1C], eax
	tp[p++] = 0x61;                                  // POPAD
	tp[p++] = 0xC3;                                  // ret

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);

	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
}

// ==================== 植物解锁判定 Hook（选卡界面）====================
// 原版"植物是否解锁"判定在 IsSeedTypeUnlocked(0x453B20) 尾部 453C17-453C24：
//   mov eax, edi(LawnApp); call 453AC0(progress2idx); cmp ebx(SeedType), eax; setl al
//   → 解锁 = (SeedType < progress2idx(PlayerInfo+0x24))
// ★ 掉落(453A90)与解锁(453AC0)是两套独立逻辑——之前只 hook 了掉落，
//   所以选卡界面仍是原版顺序解锁。本 hook 把"普通植物"的判定改为：
//   配置了 plant_unlock.ini 的植物按"已通关数 >= 配置关卡"判定，未配置走原版算术。
// 调用约定（全 16 个调用者确认）：edi = LawnApp*，ebx = SeedType，返回 al(bool)。
// 注意：紫卡(41~48)在 453B20 前半段按 PlayerInfo+0x1C4 购买标志判定，
//       不经过本 hook 点（配置紫卡解锁暂不支持，见 ini 注释）。

// 原版 453AC0（progress2idx）算术：PlayerInfo+0x24（进度）→ 0..49 索引
static int ProgressToIndex(int progress)
{
	if (progress > 50)
		return 49;
	int eax = progress - 1;
	int q = eax / 10;
	int r = eax % 10;
	int ecx = r + 1;
	eax = ecx + q * 8;
	if (ecx < 10)
	{
		if (ecx >= 5)
			eax -= 1;
	}
	else
	{
		eax -= 2;
	}
	if (eax > 0x28) eax = 0x28;
	if (eax > 0x31) eax = 0x31;
	return eax;
}

// 解锁判定（trampoline 直接 call；hook 帧内，纯内存读取，无 CRT/容器）
// ★ 二周目规则（453AC0 铁证）：通关 5-10 时 452310 写 PlayerInfo+0x24=1（进度重置）、
//   +0x2C += 1（周目计数）；原版 progress2idx 见 +0x2C>0 直接返回 49 全解锁。
//   因此配置的"一周目通关解锁"植物在二周目也必须全解锁（用户需求，与原版一致）。
//   紫卡(41~48 商店植物)在 453B20 前半段按购买标志返回，不经过本 hook，无需处理。
static int __cdecl MyIsUnlocked(int lawnApp, int seedType)
{
	int playerInfo = MemSafeRead<int>(lawnApp + 0x82c);
	if (playerInfo == 0)
		return 0;

	// 二周目及以上：普通植物全解锁（含配置的植物），同原版 453AC0 语义
	if (MemSafeRead<int>(playerInfo + 0x2c) > 0)
		return 1;

	if (seedType >= 0 && seedType < 53)
	{
		int lvl = g_unlockLevel[seedType];
		if (lvl >= 1 && lvl <= 50)
		{
			int progress = MemSafeRead<int>(playerInfo + 0x24); // 已通关数+1
			return (progress - 1 >= lvl) ? 1 : 0;
		}
	}
	// 未配置 → 原版：SeedType < progress2idx(PlayerInfo+0x24)
	int idx = ProgressToIndex(MemSafeRead<int>(playerInfo + 0x24));
	return (seedType < idx) ? 1 : 0;
}

// 安装 453C17 hook（解锁判定尾部）
// trampoline：pop esi(对应原 453C23 恢复) → PUSHAD → push ebx/push edi →
//             call MyIsUnlocked → add esp,8 → 写回 EAX 槽 → POPAD → ret
void InstallUnlockHook()
{
	DWORD hookAddr = 0x453C17;

	// 修改器共存：本 hook 不拷贝原始字节（trampoline 重实现逻辑），无跳飞风险，
	// 但仍避免覆盖修改器已装的 hook（礼貌性校验，不符则放弃安装）
	{
		BYTE cur[5];
		PVZ::Memory::ReadArray<BYTE>(hookAddr, cur, 5);
		static const BYTE kExpected[5] = { 0x8B, 0xC7, 0xE8, 0xA2, 0xFE };
		if (memcmp(cur, kExpected, 5) != 0)
		{
			CrashStr("HOOKSKIP name=Unlock site=0x453C17 (bytes changed - modifier?)\r\n");
			return;
		}
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return;

	BYTE tp[64];
	int p = 0;
	tp[p++] = 0x5E;                                  // pop esi（弹出 453B20 入口 push 保存的 esi）
	tp[p++] = 0x60;                                  // PUSHAD
	tp[p++] = 0x53;                                  // push ebx（SeedType）
	tp[p++] = 0x57;                                  // push edi（LawnApp）
	int callOff = (int)&MyIsUnlocked - (tramp + p + 5);
	tp[p++] = 0xE8; memcpy(tp + p, &callOff, 4); p += 4;   // call MyIsUnlocked
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x08;  // add esp, 8
	tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x1C; // mov [esp+0x1C], eax（写回 EAX 槽）
	tp[p++] = 0x61;                                  // POPAD
	tp[p++] = 0xC3;                                  // ret

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);

	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
}

// init() 真正实现（无 __try —— 内含 std::map 等局部对象，与 __try 同函数触发 C2712；
// __try 外壳在 init()，与 UpdatePoisonFrame/Inner 同模式）
static void initInner();
static void ExpGlyphLoadOnce();   // 经验文字字形预加载（定义在经验文字段）

// ★ 2026-09-01 加固：init 跑在注入线程里，任何未预期崩溃都会直接带崩游戏
// （8-29/9-1 两次 init 期崩溃：读 0x350 / 配置加载）。套 __try：异常落盘后吞掉，
// 已装的部分生效，未装的 hook 由各自的 installed 标志在 onGameObjectsUpdate 延迟补装。
void init()
{
	CRASH_STEP("init:enter");
	__try
	{
		initInner();
	}
	__except (CrashSwallowFilter(GetExceptionInformation()))
	{
	}
}

static void initInner()
{
	// ★ 崩溃诊断：最先装（模块表快照 + VEH），之后任何崩溃都能落到 D:\pvz_crash.log
	InstallCrashHandler();
	// ★ 2026-10-16：在这里（安全上下文）**预先打开**日志文件句柄并常驻。
	//   这样 VEH 在"堆函数内部崩溃"（堆锁已被本线程持有、堆状态不一致）时只做 WriteFile，
	//   不再 CreateFileA —— CreateFileA 会在进程堆上分配内存、重入那个不一致的堆，
	//   把一次本可存活的堆损坏放大成硬崩（日志 frames 链上 ntdll 帧重复出现即此特征）。
	CrashLogEnsureHandle();
	CRASH_STEP("init");

	// DLL 运行在游戏进程空间，应直接访问游戏内存
	PVZ::Memory::localExecute = true;

	// ★★★ 2026-09-01 崩溃修复（init+39 / pch.cpp:4039 / VEH fault=0x350 / EAX=0）：
	//   PVZ_BASE = ReadMemory<int>(0x6A9EC0)（LawnApp 实例指针）。
	//   注入时机若早于游戏初始化（游戏刚打开就注入、LawnApp 尚未创建），
	//   0x6A9EC0 处为 0 → PVZ_BASE = 0 → ReadMemory<HWND>(0x350) 直接解引用
	//   空地址 → Access Violation。这同时也是 8-29 第一次"无故崩溃"
	//  （crash.txt 里 ReadMemory EAX=0x350）的真正根因，之前一直误判。
	//   修复：PVZ_BASE 有效性 + 可读性校验，无效则 mainwindowhandle 留空
	//  （绘制期代码用 DrawUITop 入口 hook 保存的 Graphics*，不依赖该句柄；
	//   焦点检查 GetForegroundWindow 只在句柄有效时启用）。
	{
		int pvzBase = PVZ_BASE;
		if (pvzBase >= 0x400000 && CrashIsReadable((DWORD)pvzBase, 0x400))
			PVZ::Memory::mainwindowhandle = MemSafeRead<HWND>(pvzBase + 0x350);
		else
			PVZ::Memory::mainwindowhandle = NULL;
	}
	PVZ::Memory::Variable = PVZ::Memory::AllocMemory(4);

	LoadPlantTierConfig();
	LoadPlantAttackSpeedConfig();
	LoadPlantMechanicsConfig();
	LoadWaveConfig();
	LoadZombieMechanicsConfig();
	LoadPlantCostConfig();      // plant_cost.ini → 写 PlantDefinition 表（阳光/冷却，不碰攻速）
	LoadPlantUnlockConfig();    // plant_unlock.ini → 掉落关卡映射
	PlantCfgLog("[init] config load done\n");
	// 究极大喷菇：注入即落盘一行 —— 这行存在就证明"跑的是新 DLL"（排 DLL 陈旧）
	UlfDebugFlush("init");
	// InstallAwardSeedHook() 延迟到 onGameObjectsUpdate 首次执行（同花盆/冰锥模式，
	// 直接开 pvzmain.exe 时 init() 过早，0x40xxxx 区域可能仍是未映射的垃圾字节）

	// 冰锥贴图延迟到 onGameObjectsUpdate 加载（游戏资源就绪后，避免注入过早崩溃）

	// 清空上一次运行残留的数据
	g_plantExperience.clear();
	g_projectileShooterMap.clear();

	// 分配字符串缓冲区（游戏原生 DrawText 调用用）
	g_stringBuffer = PVZ::Memory::AllocMemory(0, 32);

	// Hook at 0x417DA0: edi=griditem, 用游戏原生 DrawText(0x587120) 画经验值
	{
		DWORD hookAddr = 0x417DA0;
		int rawLen = 7;  // push -01; push 0x0064807D = 7 bytes
		int codeLen = 11; // PUSHAD(1)+push edi(1)+call(5)+add esp(3)+POPAD(1)

		BYTE rawCode[7];
		PVZ::Memory::ReadArray<BYTE>(hookAddr, rawCode, rawLen);
		{
			static const BYTE kExpected[7] = { 0x6A, 0xFF, 0x68, 0x7D, 0x80, 0x64, 0x00 };
			if (memcmp(rawCode, kExpected, 7) != 0)
			{
				CrashStr("HOOKSKIP name=ExpTextDraw site=0x417DA0 (bytes changed - modifier?)\r\n");
				goto skipExpTextHook;
			}
		}

		{
		int trampoline = (int)TRAMPOLINE_ALLOC();
		if (trampoline != 0)
		{
			if (rawCode[0] == 0xE8 || rawCode[0] == 0xE9)
				*(int*)(rawCode + 1) = *(int*)(rawCode + 1) + (int)hookAddr - trampoline - codeLen - 2;

			BYTE tp[32];
			int p = 0;
			tp[p++] = 0x60;                                      // PUSHAD
			tp[p++] = 0x57;                                      // PUSH EDI (griditem)
			int callOff = (int)&onDrawExpUI - (trampoline + p + 5);  // call onDrawExpUI
			tp[p++] = 0xE8; memcpy(tp + p, &callOff, 4); p += 4;
			tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;     // add esp, 4
			tp[p++] = 0x61;                                      // POPAD
			memcpy(tp + p, rawCode, rawLen); p += rawLen;        // original code
			int jmpOff = (int)(hookAddr + rawLen) - (trampoline + p + 5);
			tp[p++] = 0xE9; memcpy(tp + p, &jmpOff, 4); p += 4;

			PVZ::Memory::WriteArray<BYTE>(trampoline, tp, p);

			int hookOff = trampoline - ((int)hookAddr + 5);
			BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
			PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
		}
		}
skipExpTextHook: ;
	}

	// 冰锥贴图 hook 延迟到 onGameObjectsUpdate 安装（游戏代码解密完成后）
	// 直接开 pvzmain.exe 时 init() 过早，0x46E6C7 处可能是垃圾字节

	// 经验文字字形资源：init 时先试一次（主菜单已加载基础资源）；
	// 若此刻资源未就绪，onGameObjectsUpdate 还会再试（最多 4 次）。
	ExpGlyphLoadOnce();

}

// 利用游戏原生 DrawText(0x587120) 绘制植物经验值数字
// gridItem(EDI) 有颜色字段: [edi+0x30]=R, [edi+0x34]=G, [edi+0x38]=B, [edi+0x3C]=A

// ★★原生 API 绘制文字（与钱币计数器 DrawUICoinBank 完全一致的方式）：
//   SetColorizeImages(0x586D10) + SetColor(0x586CC0) + SetFont + DrawString(0x587120)。
//   钱币数字用此序列显示正常颜色；mod 之前直接写 Graphics 字段颜色恒失效（黑/绿）。
//   注意：0x587120 传参约定 EAX=Graphics、栈 push y/x/str（cdecl callee 清栈）。
static void NativeDrawExpText(DWORD g, int x, int y, const char* str, int r, int gg, int b)
{
	int col[4] = { r, gg, b, 255 };
	int len = (int)strlen(str);
	PVZ::Memory::WriteArray<char>(g_stringBuffer, (char*)str, len + 1);
	// SetString(0x404330): thiscall ecx=0x72abf5, push len, push str
	__asm {
		pushad
		push len
		push g_stringBuffer
		mov ecx, 0x72abf5
		mov eax, 0x404330
		call eax
		popad
	}
	// SetColorizeImages(g, true): 0x586D10 = mov [eax+0x48], cl
	__asm {
		pushad
		mov eax, g
		mov ecx, 1
		mov ebx, 0x586D10
		call ebx
		popad
	}
	// SetColor(g, &col): 0x586CC0 = 把 col 4 int 拷到 g+0x30..3C
	__asm {
		pushad
		lea eax, col
		mov ecx, g
		mov ebx, 0x586CC0
		call ebx
		popad
	}
	// ★实验：预热——画空白图（模仿钱币绘制的 DrawImage）。
	// 日志铁证：bad/good 帧 Graphics 状态完全一致、颜色参数正确，但颜色只有
	// 钱币绘制（含 DrawImage）之后才生效 → 怀疑 DrawImage 设置 DDraw 层颜色状态。
	DWORD blankImg = MemSafeRead<int>(0x6A77BC);
	if (blankImg)
		Draw::DrawImage(0, 0, blankImg, g);
	// DrawString: push y, push x, push 0x72abf5, eax=g
	__asm {
		pushad
		push y
		push x
		push 0x72abf5
		mov eax, g
		mov ebx, 0x587120
		call ebx
		popad
	}
}

// ==================== 经验文字：自绘字形（彻底绕开 DrawString/DC 状态） ====================
//
// 【为什么不再用 DrawString】
//   0x587120 (Graphics::DrawString) 最终走字体对象：
//     Font->vtable[0x28] (0x58EAB0) -> Font->vtable[0x34] (0x58E290)
//     -> SysFont::DrawString (0x599EC0) -> GDI SelectObject + TextOutA
//   中文版实际使用的 4 个字体全局（0x6A7384/0x6A74B0/0x6A75C8/0x6A7714）运行时
//   vtable 全是 0x672614，即**所有文字最终都走 SysFont 的 GDI 路径**（.txt/图集
//   仍用于字宽等度量，但绘制是 GDI）。
//   GDI 使用的是**按 surface 全局缓存的 DC**（0x56C720 → [surface+0x70]）。该 DC
//   的映射模式/世界变换/文字颜色/字符间距会被之前的 UI 绘制（横幅、滑入动画、
//   钱币计数等）残留下来，导致 mod 文字出现"字号忽大忽小 / 颜色变黑变绿"，
//   且随绘制顺序变化（历史顽疾）。
//   单纯复制 Graphics 只能隔离 Graphics 字段，隔离不了 surface 上的 DC。
//
// 【本方案】
//   用游戏实际使用的 GDI 字体（Arial Unicode MS，20pt，与原版
//   NativeDrawExpText/HouseofTerror20 完全同款）离线把 0-9 L v . 渲染成
//   白字 + alpha 的 RGBA PNG；运行时用已验证的 DrawImage(0x587150) 逐字绘制。
//   颜色走 Graphics+0x30..0x3C + colorize(0x48)，与钱币计数器的图像绘制同一条
//   稳定路径；字号/字形完全由 PNG 像素决定，不再受任何 DC/字体状态影响。
//   dx/dy = 该字形墨迹相对 TextOutA(x,y) 原点的偏移（与 GDI 完全一致），
//   advance = GetTextExtentPoint32A 的宽度。
//
//   PNG 源文件在 pvzclass\pvzdll\assets\expfontgdi20\，build.bat 会复制到游戏
//   images\ 目录；运行时缺失则自动回退旧的 NativeDrawExpText（至少还有字）。
struct ExpGlyphDef
{
	char ch;
	unsigned char advance;
	signed char dx;      // 墨迹左边界相对 TextOutA 原点的偏移
	signed char dy;      // 墨迹上边界相对 TextOutA 原点的偏移
	const char* file;
	DWORD img;
};

static ExpGlyphDef g_expGlyphDefs[] =
{
	// 与阳光/钱币计数同款：ContinuumBold14（中文版 SysFont = Arial Unicode MS 14pt Bold）。
	// dy = 墨迹顶相对 TextOut 原点，dx = 墨迹左边界，advance = GDI 字宽。
	{ '0', 11, 0,  5, "images\\ExpFontGDI_30.png", 0 },
	{ '1', 11, 1,  5, "images\\ExpFontGDI_31.png", 0 },
	{ '2', 11, 0,  5, "images\\ExpFontGDI_32.png", 0 },
	{ '3', 11, 0,  5, "images\\ExpFontGDI_33.png", 0 },
	{ '4', 11, 0,  5, "images\\ExpFontGDI_34.png", 0 },
	{ '5', 11, 0,  5, "images\\ExpFontGDI_35.png", 0 },
	{ '6', 11, 0,  5, "images\\ExpFontGDI_36.png", 0 },
	{ '7', 11, 0,  5, "images\\ExpFontGDI_37.png", 0 },
	{ '8', 11, 0,  5, "images\\ExpFontGDI_38.png", 0 },
	{ '9', 11, 0,  5, "images\\ExpFontGDI_39.png", 0 },
	{ 'L', 11, 1,  5, "images\\ExpFontGDI_4C.png", 0 },
	{ 'v', 10, 0,  9, "images\\ExpFontGDI_76.png", 0 },
	{ '.',  6, 1, 17, "images\\ExpFontGDI_2E.png", 0 },
};

static bool g_expGlyphLoadDone = false;
static int  g_expGlyphLoadTries = 0;

static ExpGlyphDef* ExpGlyphFind(char c)
{
	for (int i = 0; i < (int)(sizeof(g_expGlyphDefs) / sizeof(g_expGlyphDefs[0])); i++)
		if (g_expGlyphDefs[i].ch == c)
			return &g_expGlyphDefs[i];
	return 0;
}

// 幂等加载；资源未就绪/缺图时有限次重试（每次 Draw::ToString 都会漏 ~1KB，
// 不能每帧重试；最多 4 次后永久回退旧文字路径）。
static void ExpGlyphLoadOnce()
{
	if (g_expGlyphLoadDone)
		return;
	if (g_expGlyphLoadTries >= 4)
	{
		g_expGlyphLoadDone = true;
		return;
	}
	g_expGlyphLoadTries++;

	bool all = true;
	__try
	{
		for (int i = 0; i < (int)(sizeof(g_expGlyphDefs) / sizeof(g_expGlyphDefs[0])); i++)
		{
			ExpGlyphDef& d = g_expGlyphDefs[i];
			if (d.img)
				continue;
			DWORD isNew = 0;
			Draw::PString variant = Draw::ToString("");
			Draw::PString fn = Draw::ToString(d.file);
			DWORD ref = Draw::GetSharedImage(isNew, variant, fn);
			if (ref != 0)
				d.img = Draw::SharedImageRefToImage(ref);
			if (!d.img)
				all = false;
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		all = false;
	}
	if (all)
		g_expGlyphLoadDone = true;

	// 完成/放弃时一次性诊断：确认字形图是否真的从 images\ 加载成功
	if (g_expGlyphLoadDone)
	{
		static bool logged = false;
		if (!logged)
		{
			logged = true;
			int ok = 0;
			for (int i = 0; i < (int)(sizeof(g_expGlyphDefs) / sizeof(g_expGlyphDefs[0])); i++)
				if (g_expGlyphDefs[i].img) ok++;
			char buf[128];
			sprintf_s(buf, "[GLYPH] load try=%d ok=%d/%d done=%d\r\n", g_expGlyphLoadTries, ok,
				(int)(sizeof(g_expGlyphDefs) / sizeof(g_expGlyphDefs[0])), g_expGlyphLoadDone ? 1 : 0);
			CrashStr(buf);
		}
	}
}

// 游戏 SysFont 的 tmAscent（font+0x4）。DrawString 的 y 是**基线**，
// 它给 TextOutA 的 cell top = y - tmAscent + 1。我们的字形是以 TextOutA 原点
// 为基准切的，所以也要先换算到同一个 cell top，才能和原版位置完全一致。
static int ExpGlyphAscent()
{
	// 用与阳光/钱币计数同款的 ContinuumBold14 字体对象（0x6A7384）
	DWORD font = MemSafeRead<DWORD>(0x6A7384);
	int a = 0;
	if (font && CrashIsReadable(font, 0x20))
		a = MemSafeRead<int>(font + 4);
	if (a < 8 || a > 80)
		a = 19;   // Arial Unicode MS 14pt Bold @96dpi 的 tmAscent 兜底
	return a;
}

// 用字形图绘制文字；返回绘制宽度（像素）。
// 调用方需保证 g 可读写（onDrawExpUI 已做 CrashIsReadable 校验）。
static int NativeDrawExpGlyphs(DWORD g, int x, int y, const char* str, int r, int gg, int b)
{
	ExpGlyphLoadOnce();

	// 一个字形都没加载成功 → 回退旧路径（可能仍有字号/颜色问题，但至少不空屏）
	bool any = false;
	for (int i = 0; i < (int)(sizeof(g_expGlyphDefs) / sizeof(g_expGlyphDefs[0])); i++)
		if (g_expGlyphDefs[i].img) { any = true; break; }
	if (!any)
	{
		NativeDrawExpText(g, x, y, str, r, gg, b);
		return 0;
	}

	// 与钱币计数器/原版 ImageFont 相同的绘制状态：NORMAL + colorize + 线性混合
	MemSafeWrite<int>(g + 0x44, 0);       // drawMode = NORMAL
	MemSafeWrite<BYTE>(g + 0x49, 0);      // fastStretch = 0
	MemSafeWrite<BYTE>(g + 0x4B, 1);      // linearBlend = 1
	MemSafeWrite<BYTE>(g + 0x48, 1);      // colorizeImages = 1

	// 两遍绘制：第一遍所有字形的黑色投影（+1,+1），第二遍正常颜色。
	// 先画完所有投影再画正文，避免后一个字的投影盖住前一个字的正文。
	int baseY = y - ExpGlyphAscent() + 1;   // 基线 y -> GDI TextOut cell top
	int width = 0;
	for (int pass = 0; pass < 2; pass++)
	{
		if (pass == 0)
		{
			MemSafeWrite<int>(g + 0x30, 0);
			MemSafeWrite<int>(g + 0x34, 0);
			MemSafeWrite<int>(g + 0x38, 0);
		}
		else
		{
			MemSafeWrite<int>(g + 0x30, r);
			MemSafeWrite<int>(g + 0x34, gg);
			MemSafeWrite<int>(g + 0x38, b);
		}
		MemSafeWrite<int>(g + 0x3C, 255);

		int pen = x;
		for (const char* p = str; *p; ++p)
		{
			ExpGlyphDef* d = ExpGlyphFind(*p);
			if (!d || !d->img)
			{
				pen += 8;                 // 未知字符（含中文）：留空，避免撞字
				continue;
			}
			int off = (pass == 0) ? 1 : 0;
			Draw::DrawImage(pen + d->dx + off, baseY + d->dy + off, d->img, g);
			pen += d->advance;
		}
		width = pen - x;
	}
	return width;
}

// 绘制期回调外壳（__try）：
// onDrawExpUI 挂在 0x417DA0（Board 绘制格子物件的路径里，edi=Graphics*）。
// ★关键：暂停/切后台时 UpdateGameObjects 会停，但**绘制路径照跑**——
//   也就是说本函数是"暂停时唯一还在跑的重型 mod 代码"，历史上"暂停切后台就崩"
//   的可疑点高度集中在这里。函数内部会读写 Graphics 的 0x04~0x7F 状态区
//   （含 0x7C 字节现场保存/恢复），指针一旦失效就是内存写花 + 崩溃。
// 加固：① 先校验 Graphics 指针可读；② 套 __try，异常只丢这一帧绘制。
static void onDrawExpUIInner(DWORD gridItem);

void onDrawExpUI(DWORD gridItem)
{
	CRASH_STEP("onDrawExpUI:enter");
	// Graphics 状态区（[+0x04, +0x80)）必须可读可写，否则下面的现场保存/恢复会写花内存
	if (!CrashIsReadable(gridItem + 0x04, 0x7C))
	{
		CRASH_STEP("onDrawExpUI:bad-graphics");
		return;
	}
	__try
	{
		onDrawExpUIInner(gridItem);
	}
	__except (CrashSwallowFilter(GetExceptionInformation()))
	{
	}
}

static void onDrawExpUIInner(DWORD gridItem)
{
	// 在绘制 hook 中处理死亡经验分配（时机稳定，已验证不崩溃）
	if (g_lastDeathRow >= 0)
	{
		DistributeRowExperience(g_lastDeathRow, 0, g_lastDeathExp);
		g_lastDeathRow = -1;
		g_lastDeathExp = 0;
	}

	int pvzBase = MemSafeRead<int>(0x6A9EC0);
	if (pvzBase < 0x400000) return;
	int boardAddress = MemSafeRead<int>(pvzBase + 0x768);
	if (!boardAddress) return;

	// ==== 排查日志 + Graphics 状态快照 ====
// g+0x04..0x7F 全量：平移(+04/+08) 浮点(+0C..1C) 裁剪(+20..2C) 颜色(+30..3C)
// 字体(+40) 状态字节(+44..4B) +0x4C 标志 +0x50..0x7F 状态栈/其他
BYTE gfxCur[0x7C];
PVZ::Memory::ReadArray<BYTE>(gridItem + 0x04, gfxCur, 0x7C);

	// 显式设置绘制状态：drawMode=NORMAL、fastStretch=0、linearBlend=1、
	// colorizeImages=1。经验文字已改为自绘字形（NativeDrawExpGlyphs），
	// 不再依赖钱币计数器"预热" DDraw/Graphics 状态——那套 hack 已移除。
	MemSafeWrite<int>(gridItem + 0x44, 0);
	MemSafeWrite<BYTE>(gridItem + 0x49, 0);
	MemSafeWrite<BYTE>(gridItem + 0x4B, 1);
	MemSafeWrite<BYTE>(gridItem + 0x48, 1);

	// 手动遍历 DataArray（不用 GetAllPlants——其 Plant(index) 构造地址不一致）
	// DataArray 是结构体数组，Slot i 的地址 = plantArray + i * 0x14C
	int plantCount = MemSafeRead<int>(boardAddress + 0xB0);  // max slots
	int plantArray = MemSafeRead<int>(boardAddress + 0xAC);  // DataArray ptr

	for (int i = 0; i < plantCount; i++)
	{
		const DWORD PLANT_SIZE = 0x14C;
		int plantAddress = plantArray + i * PLANT_SIZE;

		// NotExist 标志
		if (MemSafeRead<BYTE>(plantAddress + 0x141))
			continue;

		int row = MemSafeRead<int>(plantAddress + 0x1C);
		int col = MemSafeRead<int>(plantAddress + 0x28);

		// 过滤无效数据：行列号超出游戏范围（0-5 行, 0-8 列）
		if (row < 0 || row > 5 || col < 0 || col > 8)
			continue;

		// 跳过小喷菇分身：不显示经验值和等级文字
		if (g_puffToCell.find(plantAddress) != g_puffToCell.end())
			continue;

		// 花盆/睡莲/南瓜头：没有等阶，不绘制 Lv 和经验字样
		int uiSeedType = MemSafeRead<int>(plantAddress + 0x24);
		if (IsNoTierPlant(uiSeedType))
			continue;

		// 咖啡豆唤醒锁定的植物（保护伞等）未解锁前不绘制文字
		if (!IsPlantExpUnlocked(plantAddress, uiSeedType))
			continue;

		// 行高：五行场地 100px/行，六行场地（泳池/迷雾）85px/行（游戏原生
		// GridToYPixel 证实：Pool/Fog 返回 85*row+80，其他场景 100*row+80）。
		// 原硬编码 165+row*100 在六行场地仍按 100px 行距绘制 → 文字画歪，现按场景修正。
		int rowH = 100;
		int scene = MemSafeRead<int>(boardAddress + 0x554C); // LevelScene
		if (scene == (int)SceneType::Pool || scene == (int)SceneType::Fog)
			rowH = 85;

		int px = 25 + col * 80;
		int py = 165 + row * rowH;
		int px_15 = px + 15;

		int exp = 0, limit = 0;
		auto it = g_plantExperience.find(plantAddress);
		if (it != g_plantExperience.end())
		{
			exp = it->second;
			limit = GetSeedExperienceLimit(MemSafeRead<int>(plantAddress + 0x24));
		}

		// 计算等阶（西瓜投手卡3阶：未选路线时显示压回 2 阶，见"西瓜投手升级路线选择"）
		int dispType = MemSafeRead<int>(plantAddress + 0x24);
		int tier = MelonClampTier(plantAddress, dispType, GetPlantTier(dispType, exp));
		bool capped = (limit > 0 && exp >= limit);

		// --- 绘制等阶标签 (Lv.X) ---
		{
			// 等阶颜色：满阶金色，否则按等阶着色
			BYTE tr = capped ? 0xFF : TIER_COLOR_R[tier];
			BYTE tg = capped ? 0xDF : TIER_COLOR_G[tier];
			BYTE tb = capped ? 0x00 : TIER_COLOR_B[tier];
			// 字体：优先 HOT20，0 时退回钱币字体
			int drawFont = MemSafeRead<int>(0x6A75C8);
			if (drawFont == 0)
				drawFont = MemSafeRead<int>(0x6A7384);
			MemSafeWrite<int>(gridItem + 0x40, drawFont); // font

			char tierStr[16];
			sprintf_s(tierStr, "Lv.%d", tier);
			int tierY = py - 3;
			// ★自绘字形：不经过 DrawString / GDI / surface DC，字号与颜色恒定
			NativeDrawExpGlyphs(gridItem, px_15, tierY, tierStr, tr, tg, tb);
		}

		// --- 绘制经验值数字 ---
		{
			// 颜色：满阶金色，否则白色
			int nr = 0xFF;
			int ng = capped ? 0xDF : 0xFF;
			int nb = capped ? 0x00 : 0xFF;
			int numFont = MemSafeRead<int>(0x6A75C8);
			if (numFont == 0)
				numFont = MemSafeRead<int>(0x6A7384);
			MemSafeWrite<int>(gridItem + 0x40, numFont); // font

			char numStr[16];
			sprintf_s(numStr, "%d", exp);
			int expY = py + 14;
			// ★自绘字形：不经过 DrawString / GDI / surface DC，字号与颜色恒定
			NativeDrawExpGlyphs(gridItem, px_15, expY, numStr, nr, ng, nb);
		}

		// ===== 向日葵生产速度调整（双子向日葵走原版速度，不调整）=====
		if (MemSafeRead<int>(plantAddress + 0x24) == (int)SeedType::Sunflower && exp > 0)
		{
			float prodSpeedSec = GetPlantAttackSpeed((int)SeedType::Sunflower, tier);
			int prodIntervalCs = (int)(prodSpeedSec * 100.0f);
			// 叠加三叶草3阶攻速增益（生产冷却同样缩减）
			if (g_bloverBoostEndTime > 0 && boardAddress)
			{
				if (PVZ::Board(boardAddress).PlayingTime < g_bloverBoostEndTime)
					prodIntervalCs = (int)(prodIntervalCs * (1.0f - g_bloverSpeedBoostReduction));
			}
			int curInterval = MemSafeRead<int>(plantAddress + 0x5C);
			if (prodIntervalCs > 0 && curInterval != prodIntervalCs)
			{
				MemSafeWrite<int>(plantAddress + 0x5C, prodIntervalCs);
			}
		}

		// ===== 向日葵5阶升级为双子向日葵 =====
		if (MemSafeRead<int>(plantAddress + 0x24) == (int)SeedType::Sunflower && tier >= 5 && g_upgradeSunflowerAddr == 0)
		{
			g_upgradeSunflowerAddr = plantAddress;
			g_upgradeRow = row;
			g_upgradeCol = col;
			g_upgradeExp = exp;
		}
	}

	// 写回进入 hook 时的 Graphics 现场（本次经验文字绘制不污染
	// 后续原版 Board::DrawLevel 关卡名绘制的环境）
	PVZ::Memory::WriteArray<BYTE>(gridItem + 0x04, gfxCur, 0x7C);
}

void onAppUpdate(DWORD appAddress)
{
}

void onCoinCollect(DWORD coinAddress)
{
}

void onCoinCreate(DWORD coinAddress)
{
	// ===== 向日葵 4阶 额外生产小阳光（双子向日葵不触发）=====
	PVZ::Coin coin(coinAddress);
	if (coin.Type == CoinType::NormalSun)
	{
		int boardAddr = MemSafeRead<int>(PVZ_BASE + 0x768);
		if (boardAddr)
		{
			int coinRow = coin.Row;
			PVZ::Board board(boardAddr);
			auto plants = board.GetAllPlants();
			for (auto& plant : plants)
			{
				if (plant.Type != SeedType::Sunflower) continue;
				if ((int)plant.Row != coinRow) continue;
				auto it = g_plantExperience.find(plant.GetBaseAddress());
				if (it == g_plantExperience.end()) continue;
				int tier = GetPlantTier((int)SeedType::Sunflower, it->second);
				if (tier >= 4)
				{
					float sfX = coin.X;
					float sfY = coin.Y;
					Creator::CreateCoin(CoinType::MiniSun, (int)sfX, (int)sfY, CoinMotionType::Product);
					break;
				}
			}
		}
	}
}

void onCoinRemove(DWORD coinAddress)
{
}

int onDialogButtonDepress(int buttonId, int dialogId)
{
	return 0;
}

void onDialogDraw(DWORD graphics, Sexy::PDialog dialog)
{
}

// DrawPlantReanimEvent 回调：颜色计算后、绘制前触发
// T5胆小菇最快攻速时在此处强制IDLE，解决 onGameObjectsUpdate 被游戏重新覆盖的问题
void onDrawPlantReanim(DWORD plantAddress, DWORD animationAddress)
{
	if (plantAddress < 0x100000)
		plantAddress = 0;

	if (plantAddress != 0)
	{
		int type = 0;
		__try { type = MemSafeRead<int>(plantAddress + 0x24); }
		__except (EXCEPTION_EXECUTE_HANDLER) { return; }


		// --- 小喷菇分身缩放 ---
		if (type == SeedType::Puffshroom)
		{
			PVZ::Plant plant(plantAddress);
			if (plant.isValid())
			{
				PVZ::Animation anim = plant.GetAnimationPart1();
				DWORD ra = (DWORD)anim.GetBaseAddress();
				// ★★ 2026-10-16：GetAnimationPart1() 取不到动画时返回 INVALID_BASEADDRESS
				//    = 0x400000（= exe 镜像基址，**合法可读**，`!= 0` 拦不住）。
				//    而动画属性的 setter 走 Memory::WriteMemory → 内部会先 VirtualProtect
				//    把目标页改成可写再写 ⇒ 会把 0x400000+偏移 也就是 **PE 头** 悄悄改掉
				//    （破坏镜像头/节表 → 之后加载器相关路径行为异常）。
				//    这里要求 reanim 必须是"可写的堆对象"才允许写。
				if (ra < 0x10000 || ra == 0x400000 || ra >= 0x80000000) return;
				if (!CrashIsWritable(ra, 0xA0)) return;
				anim.XScale = 1.2f;
				anim.YScale = 1.2f;
			}
			return;
		}

		// --- T5胆小菇最快攻速免疫缩头：绘制时强制IDLE ---
		if (type == SeedType::Scaredyshroom)
		{
			PVZ::Plant plant(plantAddress);
			if (plant.isValid() && !plant.NotExist)
			{
				int pstate = (int)plant.State;
				if (pstate == PlantState::SCAREDYSHROOM_SCARED ||
				    pstate == PlantState::SCAREDYSHROOM_SCARED_IDLE)
				{
					auto stIt = g_scaredyStates.find(plantAddress);
					if (stIt != g_scaredyStates.end())
					{
						int exp = 0;
						auto expIt = g_plantExperience.find(plantAddress);
						if (expIt != g_plantExperience.end()) exp = expIt->second;
						int tier = GetPlantTier((int)SeedType::Scaredyshroom, exp);
						if (tier >= 5)
						{
							float minInt5 = GetPlantAttackSpeed((int)SeedType::Scaredyshroom, 5) * 100.0f;
							if (stIt->second.currentInterval <= minInt5 + 0.1f)
							{
								plant.State = PlantState::IDLE;
							}
						}
					}
				}
			}
			return;
		}
		return;  // 非 Puffshroom/胆小菇: 不做处理
	}

	// 备选：如果没拿到植物地址，直接在 animationAddress 上设缩放
	// animationAddress 指向 Reanimation transform 区域
	if (animationAddress > 0x100000)
	{
		__try
		{
			MemSafeWrite<float>(animationAddress + 0x24, 1.2f);
			MemSafeWrite<float>(animationAddress + 0x30, 1.2f);
		}
		__except (EXCEPTION_EXECUTE_HANDLER) {}
	}
}

// ==================== 魅惑菇机制 ====================
// 原版流程（AnimateChewSound 0x52B940 反汇编确认）：
//   僵尸啃食中取植物(0x52E780 → esi) → [esi+0x24]==12(魅惑菇) →
//   0x52B9D1: push esi; call 0x4679B0(Plant::Die) →
//   0x52B9D7: mov esi,edi; call 0x52FA60(StartMindControlled 魅惑僵尸)
// 方案：hook 0x52B9D1（6字节 = push esi; call Plant::Die），在魅惑菇死亡/魅惑生效前
//   截获 esi=魅惑菇、edi=僵尸。★不写 zombie+0x148（该字段由伤害路径维护，魅惑菇不参与）。
// 等阶效果：
//   1阶：魅惑的僵尸回满血（本体+头盔+盾牌）
//   2阶：在魅惑菇所在格额外生成一个被魅惑的普僵
//   3阶（满阶）：魅惑的本尊与额外普僵均可手动移动一次
//     左键点魅惑僵尸选中（黄框）→ 再点场地格子，僵尸瞬移到对应行/列（保留格内相对偏移）

static bool g_hypnoHookInstalled = false;         // 魅惑菇被吃 hook 延迟安装标志
// 魅惑僵尸命中框偏移（实测校准）：僵尸 X/Y 是脚部锚点，视觉身体在锚点右侧65px、下方90px
// 框宽90、高115，判定框与黄框绘制共用此组常量保证一致
#define HYPNO_HIT_DX       65
#define HYPNO_HIT_DY       90
#define HYPNO_HIT_HALF_W   45
#define HYPNO_HIT_UP      100
#define HYPNO_HIT_DOWN     15
static std::set<DWORD> g_hypnoMovableZombies;     // 仍可移动的魅惑僵尸（地址），移动一次即移除
static DWORD g_hypnoSelectedZombie = 0;           // 当前选中的魅惑僵尸（0 = 无）
static std::map<DWORD, int> g_hypnoPendingHeals;  // 待回满血：zombieAddr → tier（延迟到下一帧，防被魅惑流程覆盖）

// 魅惑生效处理实现（trampoline 调用，参数：plant=魅惑菇, zombie=啃食的僵尸）
static void HypnoShroomEatenImpl(DWORD plantAddr, DWORD zombieAddr)
{
	PVZ::Plant plant(plantAddr);
	if (!plant.isValid() || (int)plant.Type != (int)SeedType::Hypnoshroom)
		return;  // 防御：此路径本就只有魅惑菇会走

	PVZ::Zombie zombie(zombieAddr);
	if (!zombie.isValid())
		return;

	int exp = 0;
	auto it = g_plantExperience.find(plantAddr);
	if (it != g_plantExperience.end())
		exp = it->second;
	int tier = GetPlantTier((int)SeedType::Hypnoshroom, exp);

	// 1阶：魅惑时回满血（本体 + 头盔 + 盾牌）
	// ★延迟到下一帧执行：本 hook 在 StartMindControlled(0x52FA60) 之前运行，
	//   原版魅惑流程可能改写血量导致立即回血被覆盖，下一帧写入才是最后写入者
	if (tier >= 1)
	{
		g_hypnoPendingHeals[zombieAddr] = tier;
	}

	// 2阶：在魅惑菇所在格生成一个被魅惑的普僵
	DWORD extraZombie = 0;
	if (tier >= 2)
	{
		int pRow = MemSafeRead<int>(plantAddr + 0x1C);
		int pCol = MemSafeRead<int>(plantAddr + 0x28);
		PVZ::Zombie nz = Creator::CreateZombie(ZombieType::Zombie, pRow, (byte)pCol);
		extraZombie = nz.GetBaseAddress();
		if (extraZombie)
			nz.Hypnotize();
	}

	// 3阶：魅惑的本尊与额外普僵均可手动移动一次
	if (tier >= 3)
	{
		g_hypnoMovableZombies.insert(zombieAddr);
		if (extraZombie)
			g_hypnoMovableZombies.insert(extraZombie);
	}
}

// __try 外壳：异常时静默吞掉，绝不影响原版魅惑流程
static void __cdecl HypnoShroomEatenHandler(DWORD plantAddr, DWORD zombieAddr)
{
	__try
	{
		HypnoShroomEatenImpl(plantAddr, zombieAddr);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ===== 魅惑菇被吃 hook 安装 =====
// hook @ 0x52B9D1（原 6 字节 = 56 E8 D9 BF F3 FF = push esi; call 0x4679B0 Plant::Die）
// trampoline:
//   pushad; push edi(僵尸); push esi(魅惑菇); call HypnoShroomEatenHandler; add esp,8; popad;
//   push esi; call 0x4679B0（原指令回放）; jmp 0x52B9D7
// 安装前逐字节核对运行时字节（0x52xxxx 区域运行时才解密，防密文误装）
static void InstallHypnoShroomHook()
{
	const DWORD hookAddr = 0x52B9D1;
	const BYTE kExpected[6] = { 0x56, 0xE8, 0xD9, 0xBF, 0xF3, 0xFF };

	BYTE raw[6];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 6);

	if (memcmp(raw, kExpected, 6) != 0)
	{
		return;  // 不装 = 无魅惑菇加成，但绝不崩溃
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
	{
		return;
	}

	BYTE tp[64];
	int p = 0;
	// rel32 必须用 DWORD(无符号) 运算：VirtualAlloc 可能返回高地址（int 视为负数）会溢出
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; DWORD rel = (DWORD)target - ((DWORD)tramp + (DWORD)p + 4); memcpy(tp + p, &rel, 4); p += 4; };

	tp[p++] = 0x60;                                  // pushad
	tp[p++] = 0x57;                                  // push edi（僵尸）
	tp[p++] = 0x56;                                  // push esi（魅惑菇）
	putRelCall((DWORD)&HypnoShroomEatenHandler);     // call 处理器（cdecl，调用方清栈）
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x08;  // add esp,8
	tp[p++] = 0x61;                                  // popad
	tp[p++] = 0x56;                                  // push esi（原指令 1/2）
	putRelCall(0x4679B0);                            // call Plant::Die（原指令 2/2）
	tp[p++] = 0xE9;                                  // jmp 0x52B9D7
	{
		DWORD rel = (DWORD)0x52B9D7 - ((DWORD)tramp + (DWORD)p + 4);
		memcpy(tp + p, &rel, 4); p += 4;
	}

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);

	// 写 hook：5 字节 jmp + NOP 第 6 字节（原 call rel32 末字节 0xFF，防孤立字节）
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	MemSafeWrite<BYTE>(hookAddr + 5, 0x90);

	// 写回读验证
	BYTE verify[6];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, verify, 6);
	bool ok = (memcmp(verify, hook, 5) == 0) && (verify[5] == 0x90);
}

// ===== 魅惑菇3阶：手动移动 =====
// 僵尸当前所在列（由 X 像素反查；0x41C4C0 = Board::PixelToGridX，与 ExpPouchPixelToGrid 同源，
// 不能直接 E8 相对调用，必须装寄存器后间接调用）
static int HypnoPixelToGridX(int boardAddr, int x)
{
	int col = -1;
	__asm {
		mov eax, x
		mov ecx, boardAddr
		mov ebx, 0x41C4C0
		call ebx
		mov col, eax
	}
	return col;
}

// 僵尸是否仍是有效的可移动魅惑僵尸（未移除且仍被魅惑；无效则顺带清出集合）
static bool HypnoZombieStillMovable(DWORD zombieAddr)
{
	auto it = g_hypnoMovableZombies.find(zombieAddr);
	if (it == g_hypnoMovableZombies.end())
		return false;
	PVZ::Zombie z(zombieAddr);
	if (!z.isValid() || z.NotExist || !z.Hypnotized)
	{
		g_hypnoMovableZombies.erase(it);
		return false;
	}
	return true;
}

// 魅惑僵尸点击处理实现（返回 1 = 拦截本次点击）
// 已选中 → 本次点击 = 移动目标格；未选中 → 命中可移动魅惑僵尸则选中
static int HypnoHandleMouseDownImpl(DWORD boardAddr, int x, int y)
{
	if (g_hypnoMovableZombies.empty())
		return 0;

	// 已有选中 → 移动到点击的格子
	if (g_hypnoSelectedZombie)
	{
		DWORD zAddr = g_hypnoSelectedZombie;
		g_hypnoSelectedZombie = 0;
		if (!HypnoZombieStillMovable(zAddr))
		{
			return 0;
		}

		int col = -1, row = -1;
		if (!ExpPouchPixelToGrid(boardAddr, x, y, &col, &row))
		{
			return 0;  // 点到场地外：仅取消选中，放行
		}

		PVZ::Zombie z(zAddr);
		PVZ::Board board(boardAddr);
		int curRow = (int)z.Row;
		int curCol = HypnoPixelToGridX(boardAddr, (int)z.X);
		if (curCol < 0) curCol = 0;
		if (curCol > 8) curCol = 8;

		// 按目标格与当前格的像素差平移：保留格内相对偏移，行高自动适配泳池/屋顶
		int dX = board.GridToXPixel(row, col) - board.GridToXPixel(curRow, curCol);
		int dY = board.GridToYPixel(row, col) - board.GridToYPixel(curRow, curCol);
		z.Row = row;
		z.X = z.X + dX;
		z.Y = z.Y + dY;

		g_hypnoMovableZombies.erase(zAddr);  // 每个僵尸只能移动一次
		return 1;
	}

	// 未选中 → 命中可移动的魅惑僵尸则选中
	PVZ::Board board(boardAddr);
	auto zombies = board.GetAllZombies();
	for (auto& z : zombies)
	{
		if (z.NotExist)
			continue;
		DWORD addr = z.GetBaseAddress();
		if (!g_hypnoMovableZombies.count(addr))
			continue;
		if (!z.Hypnotized)
		{
			g_hypnoMovableZombies.erase(addr);
			continue;
		}
		float zx = z.X + HYPNO_HIT_DX, zy = z.Y + HYPNO_HIT_DY;  // 锚点→视觉身体中心偏移
		if (x >= zx - HYPNO_HIT_HALF_W && x <= zx + HYPNO_HIT_HALF_W
			&& y >= zy - HYPNO_HIT_UP && y <= zy + HYPNO_HIT_DOWN)
		{
			g_hypnoSelectedZombie = addr;
			return 1;
		}
	}
	return 0;
}

// __try 外壳（Impl 含 std::vector 局部对象，C2712 要求分离）
static int HypnoHandleMouseDown(DWORD boardAddr, int x, int y)
{
	__try
	{
		return HypnoHandleMouseDownImpl(boardAddr, x, y);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		return 0;  // 异常放行原版
	}
}

// 选中僵尸黄框高亮（onDrawUITop 调用）
static void DrawHypnoSelectionUI()
{
	if (!g_hypnoSelectedZombie)
		return;
	DWORD g = (g_expPouchGStore != 0)
		? MemSafeRead<DWORD>(g_expPouchGStore) : 0;
	if (!g || !ExpPouchGraphicsValid(g))
		return;

	PVZ::Zombie z(g_hypnoSelectedZombie);
	if (!z.isValid() || z.NotExist)
	{
		g_hypnoSelectedZombie = 0;
		return;
	}
	Draw::DrawRect((int)z.X - HYPNO_HIT_HALF_W + HYPNO_HIT_DX,
		(int)z.Y - HYPNO_HIT_UP + HYPNO_HIT_DY,
		HYPNO_HIT_HALF_W * 2, HYPNO_HIT_UP + HYPNO_HIT_DOWN, g);
}

// ==================== 粒子特效预览器 ====================
// 用途：把数值表"特效"表（0x00~0x69 共 106 个粒子系统）在游戏里逐个播放，
//       配合屏幕文字提示，找出想要的特效 ID。
// 操作：F5 = 开关（开启后自动轮播 1.5s/个）；F6 = 下一个；F7 = 上一个
// 原理：PVZ::CreateParticleSystem(0x453C80) 按 EffectType 直接创建粒子系统；
//       切换前 GetAllParticleSystem()+Die() 清场（防止持续型特效堆积在场上）。
static const char* g_pfxNames[106] =
{
	"西瓜：破裂", "冰瓜：破裂", "大喷：喷出", "玉米炮：破裂", "樱桃：爆炸",
	"小丑：爆炸", "僵尸头：掉落", "僵尸手：掉落", "路障：掉落", "铁桶：掉落",
	"橄榄球头盔：掉落", "旗帜：掉落", "铁门：掉落", "报纸：掉落", "矿工帽：掉落",
	"锤子：锤僵尸", "跳跳：失去跳杆", "僵尸眼镜：掉落", "气球僵尸头：掉落",
	"土壤：飞扬1", "土壤：飞扬2", "土壤：飞扬3", "水：水花", "僵尸：从墓碑伸手",
	"土壤：飞扬4", "土壤：飞扬5", "水：水花2", "星星：1", "箭头：指向", "星星：2",
	"毁灭菇：爆炸", "土壤：飞扬6", "土壤：飞扬7", "土壤：飞扬8", "水池：潋滟",
	"土壤：飞扬9", "土壤：飞扬A", "豌豆：破裂", "黄油：破裂", "僵尸豌豆：破裂",
	"孢子：破裂", "星星：破裂", "寒冰菇：爆炸", "冰豌豆：破裂", "？？：破裂",
	"雪花：1", "光：闪耀1", "光：闪耀2", "土豆雷：爆炸", "土壤：飞扬B",
	"孢子：射出", "孢子：射出2", "卡槽：闪耀", "土壤：飞扬C", "梯子：掉落",
	"箭头：指向2", "篮球车：发射", "？？？：冰", "冰冻：解开", "车：冒烟",
	"曾哥：喷出", "跳跳僵尸头：掉落", "土壤：冒烟", "冰车：爆炸1", "冰车：爆炸2",
	"篮球车：爆炸", "皇帝的新效果", "雪花：2", "？？？", "同44",
	"看**特效", "模仿者特效", "普僵头：掉落", "普僵手臂：掉落", "普僵头：掉落2",
	"火焰（向前方）", "火焰（一圈）", "雪花四散", "冰球留下的痕迹", "火球（其余4E）",
	"将亡：爆炸", "屏幕一闪", "星光点点闪烁", "雪花：飞扬", "雪花：",
	"光斑", "更大一点的55", "火星泛泛", "魅惑菇特效", "普通罐子：破裂",
	"植物罐子：破裂", "僵尸罐子：破裂", "光晕+箭头（指向下方）", "水中僵尸头上的珊瑚",
	"mustache胡子：掉落", "future眼镜：掉落", "pinata的糖果", "类似于一小条水蒸气",
	"冰车：尾气1", "sukhbir的花朵", "屏幕两闪", "闪光（GHTR土豆雷）", "僵尸圈",
	"拿到钱袋类似特效", "雾霾（雾）", "箭头（指向下方）"
};
static_assert(sizeof(g_pfxNames) / sizeof(g_pfxNames[0]) == 106, "pfx name count must be 106");
static bool  g_pfxPreviewActive = false;   // 预览模式开关
static bool  g_pfxPreviewAuto   = true;    // 自动轮播
static int   g_pfxPreviewIndex  = 0;       // 当前特效 ID (0..105)
static int   g_pfxPrevF5 = 0, g_pfxPrevF6 = 0, g_pfxPrevF7 = 0; // 按键沿检测
static DWORD g_pfxLastSwitchCs = 0;        // 上次切换的 PlayingTime（厘秒）
static const int PFX_HOLD_CS = 150;        // 每个特效停留 1.5 秒
static const int PFX_COUNT = 106;

// ============================================================================
// ★★ 2026-09-01 崩溃根因修复 ================================================
//  原实现：调用 PVZ::GetAllParticleSystem() 遍历"场上所有"粒子系统并逐个 Die()。
//  但 PVZClass 的 TodParticleSystem 布局与游戏真实布局**完全不符**：
//      框架假设：array=[[LawnApp+0x820]+0]、stride=0x2C、Dead@0x1C、Id@0x28
//      游戏真实（Reanimation::Update 内 0x464410 反汇编铁证）：
//          holder    = [LawnApp + 0x820]
//          DataArray = [holder + 8]
//          block     = [DataArray + 0]     count = [DataArray + 8]
//          stride    = 0xA0 (160 字节)      Id   = +0x9C
//  于是原实现对一堆**野地址**执行 `push 野地址; call 0x5160C0(Die)`，
//  游戏会把任意内存当成 TodParticleSystem 结构体来拆解 → 大规模内存破坏，
//  表现为：0xFEEEFEEE（已释放内存）、EIP 落 ntdll、崩溃点随机、偶发难复现。
//
//  修复原则：
//   ① **只清理预览器自己创建的那一个粒子系统**（记录地址），绝不遍历全局；
//   ② 绝不碰游戏自己的粒子系统 —— 杀掉它们会让 GameObject 的 attachmentID
//      （僵尸冰道/魅惑光环/植物光环等）悬空 → 后续 Reanimation::Update 查
//      attachment 时读到野指针 → use-after-free 崩溃。
// ============================================================================
static DWORD g_pfxOwnedAddr = 0;   // 预览器自己创建的粒子系统地址（0=无）

static void PfxClearAll()
{
	DWORD addr = g_pfxOwnedAddr;
	g_pfxOwnedAddr = 0;
	if (addr == 0)
		return;
	// 只对自己创建过的地址操作；先做可读性校验（跨页递归，纯 Win32）
	if (!CrashIsReadable(addr, 0xA0))
		return;
	__try
	{
		PVZ::TodParticleSystem ps(addr);
		// 注意：不读 ps.Dead —— 框架里 Dead@0x1C 这个偏移未经本版本验证，
		// 用它做判断反而可能误判。Die() 内部本身有检查，直接调即可。
		ps.Die();
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 播放第 idx 个特效（先清掉自己上一次创建的）。无效 ID 创建失败也无害，不崩。
static void PfxPlay(int idx)
{
	// 诊断（仅首次写一次）：确认预览器确实被激活过，用于排除"F5 误触发"歧义
	static bool s_loggedActivate = false;
	if (!s_loggedActivate)
	{
		s_loggedActivate = true;
		CrashStr("PFX: particle previewer ACTIVATED\r\n");
	}

	PfxClearAll();
	__try
	{
		PVZ::TodParticleSystem ps =
			PVZ::CreateParticleSystem(400.0f, 270.0f, 0x618A0, (EffectType::EffectType)idx);
		DWORD addr = ps.GetBaseAddress();
		// 只登记预览器自己创建的粒子系统，供下次清理（绝不登记游戏自己的）
		if (addr != 0 && CrashIsReadable(addr, 0xA0))
			g_pfxOwnedAddr = addr;
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 每帧轮询：按键 + 自动轮播（onGameObjectsUpdate 调用，仅关卡内生效）
static void UpdateParticlePreviewer(DWORD boardAddress)
{
	// ★ 焦点检查（2026-09-01）：GetAsyncKeyState 是**全局**的，
	//   在其他窗口按 F5（比如刷新网页）也会被这里读到"按下"。
	//   这会让预览器在用户毫无察觉的情况下被激活，进而触发清场逻辑。
	//   只在游戏窗口处于前台时才响应快捷键；失焦时清零沿状态，
	//   避免"切出去按了 F5、切回来立刻触发一次"的误激活。
	HWND gameWnd = PVZ::Memory::mainwindowhandle;
	if (gameWnd != NULL && GetForegroundWindow() != gameWnd)
	{
		g_pfxPrevF5 = g_pfxPrevF6 = g_pfxPrevF7 = 0;
		return;
	}

	int f5 = (GetAsyncKeyState(VK_F5) & 0x8000) ? 1 : 0;
	int f6 = (GetAsyncKeyState(VK_F6) & 0x8000) ? 1 : 0;
	int f7 = (GetAsyncKeyState(VK_F7) & 0x8000) ? 1 : 0;

	if (f5 && !g_pfxPrevF5)      // F5 沿：开关预览
	{
		g_pfxPreviewActive = !g_pfxPreviewActive;
		g_pfxLastSwitchCs = 0;
		if (g_pfxPreviewActive) PfxPlay(g_pfxPreviewIndex);
		else PfxClearAll();
	}
	else if (f6 && !g_pfxPrevF6) // F6 沿：下一个特效
	{
		g_pfxPreviewIndex = (g_pfxPreviewIndex + 1) % PFX_COUNT;
		if (g_pfxPreviewActive) { PfxPlay(g_pfxPreviewIndex); g_pfxLastSwitchCs = 0; }
	}
	else if (f7 && !g_pfxPrevF7) // F7 沿：上一个特效
	{
		g_pfxPreviewIndex = (g_pfxPreviewIndex + PFX_COUNT - 1) % PFX_COUNT;
		if (g_pfxPreviewActive) { PfxPlay(g_pfxPreviewIndex); g_pfxLastSwitchCs = 0; }
	}
	g_pfxPrevF5 = f5; g_pfxPrevF6 = f6; g_pfxPrevF7 = f7;

	// 自动轮播：到点自动播放下一个
	if (g_pfxPreviewActive && g_pfxPreviewAuto)
	{
		int playingTime = MemSafeRead<int>(boardAddress + 0x5568);
		if (g_pfxLastSwitchCs == 0)
			g_pfxLastSwitchCs = playingTime;
		else if (playingTime - g_pfxLastSwitchCs >= PFX_HOLD_CS)
		{
			g_pfxLastSwitchCs = playingTime;
			g_pfxPreviewIndex = (g_pfxPreviewIndex + 1) % PFX_COUNT;
			PfxPlay(g_pfxPreviewIndex);
		}
	}
}

// 绘制预览提示（onDrawUITop 调用）
static void DrawParticlePreviewUI()
{
	if (!g_pfxPreviewActive)
		return;
	DWORD g = (g_expPouchGStore != 0) ? MemSafeRead<DWORD>(g_expPouchGStore) : 0;
	if (!g || !ExpPouchGraphicsValid(g))
		return;
	__try
	{
		char buf[64];
		sprintf_s(buf, sizeof(buf), "特效 %d/%d %s", g_pfxPreviewIndex, PFX_COUNT - 1, g_pfxNames[g_pfxPreviewIndex]);
		if (strlen(buf) > 30) buf[30] = 0;   // g_stringBuffer 仅 32 字节，防越界
		NativeDrawExpText(g, 20, 24, buf, 255, 255, 255);
		NativeDrawExpText(g, 20, 44, "F5开关  F6下一个  F7上一个", 0, 255, 0);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 顶层 UI 绘制（DrawUITop 事件）。暂停/切后台时绘制路径照跑，同样需要防崩溃外壳。
static void onDrawUITopInner(DWORD graphics)
{
	DrawExpPouchUI();
	DrawMarigoldUI();  // 金盏花：悬浮产出物 / 选中跟随 / 杀虫剂区域 / 留声机加成
	DrawGbUI();        // 墓碑吞噬者：悬浮经验包 / 选中跟随
	DrawHypnoSelectionUI();  // 魅惑菇3阶：选中的魅惑僵尸黄框高亮
	DrawParticlePreviewUI(); // 粒子特效预览器：当前特效编号/名称提示
	DrawMelonChooseUI();     // 西瓜投手：升级路线选择窗口（面板+待机动画+方案按钮）
	DrawGarlicArrows();      // 大蒜2阶：换行方向箭头（右下角）
	DrawMagnetShields();     // 磁力菇1阶：护盾贴图 + 3阶飞行中的铁器
}

void onDrawUITop(DWORD graphics)
{
	// 经验包 UI：graphics 参数（DrawUITopEvent 的 [esp+40]）是调用者栈深处、不可靠，
	// 实际使用 DrawUITop 入口 hook(0x41AA40) 保存的本帧 Graphics*（堆存储 g_expPouchGStore）
	CRASH_STEP("onDrawUITop:enter");
	__try
	{
		onDrawUITopInner(graphics);
	}
	__except (CrashSwallowFilter(GetExceptionInformation()))
	{
	}
}

int onDrawZombieReanim(DWORD zombieAddress, DWORD animationAddress)
{
	return 0;
}

// ==================== 关卡进度植物经验存档系统 ====================
// 原版游戏退出/关闭窗口时会保存关卡进度（植物布局/阳光/波次），但植物经验值是
// DLL 内部状态（g_plantExperience 按植物地址索引，重进关卡地址全变）→ 原本退出即丢。
// 本系统：
//   ① 轮询帧周期性把场上植物经验快照落盘 plant_exp_save.dat（DLL/游戏目录）
//      —— 布局变化（种植/铲除/死亡）会立即标脏下一帧补写，退出窗口时最多丢几秒经验
//   ② 关卡开始（onBoardInitAfter/onNewGame）挂起还原标记，轮询帧逐帧尝试还原：
//      关卡标识 + 植物布局(type,row,col 多重集合) 完全一致才按 (类型,行,列)
//      把经验写回当前植物地址；恢复流程逐帧补建植物，不齐时在重试窗口内等待
//   ③ 还原成功/判定作废后删除存档文件，防止同关卡重开时误还原
//   （咖啡豆唤醒标记一并存还原；日志写 D:\pvz_expsave.log 便于排查）
struct PlantExpSaveEntry
{
	int type;       // SeedType
	int row;
	int col;
	int exp;        // 经验值
	int awakened;   // 咖啡豆唤醒标记（保护伞/金盏花），1=已唤醒；
	               // ★小喷菇首领专用：改存"整格集群唤醒"标记（小喷菇非咖啡豆锁定植物，
	               //  该字段对分身/首领恒为0，可安全复用）
	int role;       // 小喷菇专用：-1=非小喷菇（或旧格式行），0=首领（持经验），1-4=分身槽位
	int route;      // 升级路径选择：0=未选/无路线机制，1/2=已选路线A/B（西瓜；未来杨桃等复用此字段）
	long long key;  // (type<<32)|(row<<16)|col，布局比对用
	bool used;      // 本轮匹配消耗标记
};

static const char* PLANT_EXP_SAVE_FILE = "plant_exp_save.dat";
static const int EXP_SAVE_INTERVAL = 300;      // 周期落盘间隔（轮询帧）
static const int EXP_SAVE_DIRTY_INTERVAL = 60;  // 布局变化后补写节流
static const int EXP_SAVE_RESTORE_WINDOW = 900; // 还原窗口（帧）：正常 resume 植物恢复在开局后很快完成；
// ★故意不设太长：输关重开/新开局时用户重新种植若在窗口内摆出与快照完全相同的布局会误还原，
//   窗口过长会放大该风险（正常开局有选卡耗时，通常耗不尽窗口）

static bool g_expSaveRestorePending = false;   // 关卡开始后待尝试还原
static int g_expSaveRestoreDeadline = 0;       // 还原重试剩余帧数
static bool g_expSaveSnapshotLoaded = false;   // 快照已从文件读入内存
static std::string g_expSaveSnapshotLevel;    // 快照的关卡标识
static std::vector<PlantExpSaveEntry> g_expSaveSnapshotEntries;
static int g_expSaveAutosaveCounter = 0;      // 距上次落盘的帧数
static bool g_expSaveDirty = false;           // 布局变化标记（下帧补写）
static bool g_expSaveLoggedThisLevel = false;  // 本关是否已写过首条存档日志

// 存档系统日志（仅轮询帧等安全上下文调用，同 PlantCfgLog 套路；带时间戳便于排查）
static void PlantExpSaveLog(const char* fmt, ...)
{
	FILE* f = fopen("D:\\pvz_expsave.log", "a");
	if (!f)
		return;
	SYSTEMTIME st;
	GetLocalTime(&st);
	fprintf(f, "[%02d:%02d:%02d] ", st.wHour, st.wMinute, st.wSecond);
	va_list ap;
	va_start(ap, fmt);
	vfprintf(f, fmt, ap);
	va_end(ap);
	fclose(f);
}

// 获取 DLL(=游戏)目录下文件的完整路径（防快捷方式启动 CWD 不对，同 OpenConfigFile）
static std::string GetGameDirFilePath(const char* name)
{
	char dllPath[MAX_PATH] = { 0 };
	HMODULE hMod = NULL;
	GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
		(LPCSTR)&GetGameDirFilePath, &hMod);
	GetModuleFileNameA(hMod, dllPath, MAX_PATH);
	std::string dir = dllPath;
	size_t pos = dir.find_last_of('\\');
	if (pos != std::string::npos)
		dir = dir.substr(0, pos);
	return dir + "\\" + name;
}

static long long PlantExpSaveMakeKey(int type, int row, int col)
{
	return ((long long)type << 32) | ((long long)row << 16) | (long long)col;
}

// 把当前场上植物经验快照写入存档文件（只允许轮询帧调用——崩溃铁律）
// 先写 .tmp 再替换，防止进程中途被杀留下半截文件
static void PlantExpSaveWriteFile(DWORD boardAddress)
{
	PVZ::Board board(boardAddress);
	if (!board.GetBaseAddress())
		return;

	std::string levelKey = MakeLevelKey(board);

	std::vector<PlantExpSaveEntry> entries;
	auto plants = board.GetAllPlants();
	for (auto& plant : plants)
	{
		if (!plant.isValid())
			continue;
		PlantExpSaveEntry e;
		e.type = (int)plant.Type;
		e.row = (int)plant.Row;
		e.col = (int)plant.Column;
		int addr = plant.GetBaseAddress();
		auto it = g_plantExperience.find(addr);
		e.exp = (it != g_plantExperience.end()) ? it->second : 0;
		e.awakened = (g_coffeeAwakenedPlants.count(addr) > 0) ? 1 : 0;
		e.role = -1;
		e.route = PlantPathGetRoute((int)plant.Type, addr);   // 升级路径：西瓜已选路线(1/2)/未选0
		// 小喷菇集群：记录首领/分身槽位（读档还原集群结构用）；
		// 首领的 awakened 字段改存"整格集群唤醒"标记（clusterAwake）
		if (plant.Type == SeedType::Puffshroom)
		{
			int cellKey = e.row * 10 + e.col;
			auto cit = g_puffClusters.find(cellKey);
			if (cit != g_puffClusters.end())
			{
				if (cit->second.plants[0] == (DWORD)addr)
				{
					e.role = 0;
					e.awakened = cit->second.clusterAwake ? 1 : 0;
				}
				else
				{
					for (int i = 1; i < 5; i++)
					{
						if (cit->second.plants[i] == (DWORD)addr)
						{
							e.role = i;
							break;
						}
					}
				}
			}
		}
		e.key = PlantExpSaveMakeKey(e.type, e.row, e.col);
		e.used = false;
		// 花盆/睡莲/南瓜头也写入：布局指纹需要完整植物集合，还原时再过滤
		entries.push_back(e);
	}

	std::string tmpPath = GetGameDirFilePath("plant_exp_save.tmp");
	std::string finalPath = GetGameDirFilePath(PLANT_EXP_SAVE_FILE);
	{
		std::ofstream f(tmpPath.c_str());
		if (!f.is_open())
			return;
		f << "Level=" << levelKey << "\n";
		f << "Sun=" << board.Sun << "\n";
		f << "Time=" << board.PlayingTime << "\n";
		f << "Plants=" << (int)entries.size() << "\n";
		for (auto& e : entries)
			f << e.type << " " << e.row << " " << e.col << " " << e.exp << " " << e.awakened << " " << e.role << " " << e.route << "\n";
	}
	if (!MoveFileExA(tmpPath.c_str(), finalPath.c_str(), MOVEFILE_REPLACE_EXISTING))
		PlantExpSaveLog("[save] !! move tmp->final failed, err=%d\n", GetLastError());

	if (!g_expSaveLoggedThisLevel)
	{
		g_expSaveLoggedThisLevel = true;
		PlantExpSaveLog("[save] level=%s plants=%d -> %s\n",
			levelKey.c_str(), (int)entries.size(), finalPath.c_str());
	}
}

// 读入存档快照到内存。返回 false = 无文件或解析失败（视为无存档，还原结束）
static bool PlantExpSaveLoadSnapshot()
{
	std::ifstream f(GetGameDirFilePath(PLANT_EXP_SAVE_FILE).c_str());
	if (!f.is_open())
		return false;

	g_expSaveSnapshotEntries.clear();
	std::string line;
	while (std::getline(f, line))
	{
		if (line.rfind("Level=", 0) == 0)
		{
			g_expSaveSnapshotLevel = line.substr(6);
			// 去掉行尾可能混入的 \r
			while (!g_expSaveSnapshotLevel.empty() &&
				(g_expSaveSnapshotLevel.back() == '\r' || g_expSaveSnapshotLevel.back() == '\n'))
				g_expSaveSnapshotLevel.pop_back();
		}
		else if (!line.empty() && line[0] >= '0' && line[0] <= '9')
		{
			PlantExpSaveEntry e;
			std::istringstream iss(line);
			e.role = -1;
			e.route = 0;
			if (iss >> e.type >> e.row >> e.col >> e.exp >> e.awakened)
			{
				// role 为第6字段，旧格式行（5字段）缺省 -1
				if (!(iss >> e.role))
					e.role = -1;
				// route 为第7字段，缺省 0（旧存档无升级路线信息）
				if (!(iss >> e.route))
					e.route = 0;
				e.key = PlantExpSaveMakeKey(e.type, e.row, e.col);
				e.used = false;
				g_expSaveSnapshotEntries.push_back(e);
			}
		}
	}
	f.close();
	return !g_expSaveSnapshotLevel.empty();
}

// 结束本次还原尝试（清状态，可选删文件）
// keepMemory=true（还原成功路径）：内存快照保留，供 onNewGame 触发后 re-arm 重新还原
static void PlantExpSaveFinishRestore(bool deleteFile, const char* reason, bool keepMemory = false)
{
	if (deleteFile)
		DeleteFileA(GetGameDirFilePath(PLANT_EXP_SAVE_FILE).c_str());
	PlantExpSaveLog("[restore] %s (entries=%d)\n",
		reason, (int)g_expSaveSnapshotEntries.size());
	g_expSaveRestorePending = false;
	if (keepMemory)
		return;   // 保留 snapshotLoaded/entries/level（onNewGame re-arm 用）
	g_expSaveSnapshotLoaded = false;
	g_expSaveSnapshotEntries.clear();
	g_expSaveSnapshotLevel.clear();
}

// 逐帧尝试还原（轮询帧调用）。恢复流程逐帧补建植物，布局不齐时保持 pending 等下一帧
static void PlantExpTryRestore(DWORD boardAddress)
{
	if (!g_expSaveSnapshotLoaded)
	{
		if (!PlantExpSaveLoadSnapshot())
		{
			// 无存档文件：正常新开局，无需还原
			g_expSaveRestorePending = false;
			return;
		}
		g_expSaveSnapshotLoaded = true;
		PlantExpSaveLog("[restore] file loaded: level=%s entries=%d\n",
			g_expSaveSnapshotLevel.c_str(), (int)g_expSaveSnapshotEntries.size());
	}

	PVZ::Board board(boardAddress);
	if (!board.GetBaseAddress())
		return;   // board 还没好，下帧再试

	// ★ 关卡数据就绪门（与 TryApplyWaveConfig 同款）：WaveCount>0 之前
	//   AdventureLevel 尚未正确写入，关卡校验会误判 → 等待，不轻易作废
	if (board.WaveCount <= 0)
		return;

	// 校验①：关卡标识必须一致（不同关卡/模式的旧快照直接作废）
	std::string curKey = MakeLevelKey(board);
	if (curKey != g_expSaveSnapshotLevel)
	{
		PlantExpSaveFinishRestore(true, "discard: level mismatch (cur != saved)");
		return;
	}

	// 校验②：植物布局(type,row,col 多重集合)完全一致
	auto plants = board.GetAllPlants();
	size_t snapCount = g_expSaveSnapshotEntries.size();
	if (plants.size() > snapCount)
	{
		// 场上植物比快照还多：绝不可能是还原流程，立即作废
		PlantExpSaveFinishRestore(true, "discard: board plants > snapshot");
		return;
	}
	if (plants.size() < snapCount)
		return;   // 恢复流程可能还在逐帧补建植物，等下一帧

	// 数量相等：逐株配对（每株植物消耗一个同 key 的未用快照条目），
	// 先全部配对成功才写经验，防止半路不匹配时污染经验表
	std::vector<std::pair<PVZ::Plant, int>> pairs;   // (植物, 快照条目下标)
	pairs.reserve(plants.size());
	bool allMatched = true;
	for (auto& plant : plants)
	{
		if (!plant.isValid())
		{
			allMatched = false;
			break;
		}
		long long key = PlantExpSaveMakeKey((int)plant.Type, (int)plant.Row, (int)plant.Column);
		int hitIdx = -1;
		for (size_t i = 0; i < g_expSaveSnapshotEntries.size(); i++)
		{
			if (!g_expSaveSnapshotEntries[i].used && g_expSaveSnapshotEntries[i].key == key)
			{
				g_expSaveSnapshotEntries[i].used = true;
				hitIdx = (int)i;
				break;
			}
		}
		if (hitIdx < 0)
		{
			allMatched = false;
			break;
		}
		pairs.push_back({ plant, hitIdx });
	}
	if (!allMatched)
	{
		// 数量相等但布局不同：恢复流程已结束（数量只会递增），不可能再匹配
		PlantExpSaveFinishRestore(true, "discard: layout mismatch");
		return;
	}

	// ===== 全部校验通过：按 (类型,行,列) 把经验写回当前植物地址 =====
	// ★小喷菇特殊处理：同一格所有小喷菇 key 相同，经验必须只写首领（集群逻辑只认
	//   plants[0] 的经验），分身不建经验条目，且集群结构（首领/槽位/偏移/唤醒）要从
	//   快照整体重建（resume 期间 onPlantCreate 会产生残缺集群或漏建）
	struct PuffRestoreCell
	{
		DWORD leader = 0;
		int exp = 0;
		int awake = 0;                // 整格唤醒标记（存于首领条目的 awakened 字段）
		DWORD slot[5] = { 0, 0, 0, 0, 0 };   // slot[1-4]=分身植物地址
	};
	std::map<int, PuffRestoreCell> puffCells;
	int restored = 0;
	for (auto& pr : pairs)
	{
		PVZ::Plant& plant = pr.first;
		PlantExpSaveEntry& e = g_expSaveSnapshotEntries[pr.second];
		int type = (int)plant.Type;
		// 花盆/睡莲/南瓜头/咖啡豆没有等阶，不建经验条目
		if (IsNoTierPlant(type))
			continue;
		int addr = plant.GetBaseAddress();
		if (addr < 0x10000)   // 哨兵地址防御（同 InitPlantExperience）
			continue;

		// 小喷菇：登记到所在格，经验/集群重建延后统一处理
		if (type == (int)SeedType::Puffshroom && e.role >= 0)
		{
			PuffRestoreCell& cell = puffCells[e.row * 10 + e.col];
			if (e.role == 0)
			{
				cell.leader = addr;
				cell.exp = e.exp;
				cell.awake = e.awakened;
			}
			else if (e.role >= 1 && e.role <= 4)
			{
				cell.slot[e.role] = addr;
			}
			continue;
		}

		if (e.awakened)
			g_coffeeAwakenedPlants.insert(addr);   // 咖啡豆唤醒标记一并还原
		// 咖啡豆锁定且未唤醒的植物不建经验条目（同 onPlantCreate 的初始化规则）
		if (!IsPlantExpUnlocked((DWORD)addr, type))
			continue;
		g_plantExperience[addr] = e.exp;
		restored++;
		// 升级路径：还原该株已选路线（西瓜卡3阶解锁；杨桃等未来机制走同分支）
		PlantPathRestoreRoute(type, addr, e.route);
	}

	// 小喷菇集群重建（覆盖 resume 期间产生的残缺/缺失状态）
	int puffCellsRestored = 0;
	for (auto& kv : puffCells)
	{
		int cellKey = kv.first;
		PuffRestoreCell& cell = kv.second;
		if (cell.leader == 0)
			continue;   // 无首领条目（异常快照）：不动该格，防半重建

		// 经验条目：首领独占（resume 期间 onPlantCreate 可能给每个小喷菇都建了 0 经验 → 清掉）
		g_plantExperience.erase(cell.leader);
		for (int i = 1; i < 5; i++)
		{
			if (cell.slot[i])
				g_plantExperience.erase(cell.slot[i]);
		}
		g_plantExperience[cell.leader] = cell.exp;
		restored++;

		// 首领：归位基准位置（无偏移）
		PVZ::Plant leader(cell.leader);
		int leaderLayer = 0;
		if (leader.isValid() && !leader.NotExist)
		{
			leader.ImageXOffset = 0;
			leader.ImageYOffset = 0;
			leaderLayer = leader.Layer;
		}

		// 分身：重刷专属偏移与图层（游戏存档不保证保存这些字段）
		PuffshroomCluster cl;
		cl.plants[0] = cell.leader;
		for (int i = 1; i < 5; i++)
		{
			if (!cell.slot[i])
				continue;
			PVZ::Plant clone(cell.slot[i]);
			if (clone.isValid() && !clone.NotExist)
			{
				clone.ImageXOffset = PUFF_CLONE_OFFSETS[i - 1].dx;
				clone.ImageYOffset = PUFF_CLONE_OFFSETS[i - 1].dy;
				clone.Layer = leaderLayer + PUFF_CLONE_OFFSETS[i - 1].layerDelta;
			}
			cl.plants[i] = cell.slot[i];
			g_puffToCell[cell.slot[i]] = cellKey;
		}
		cl.maxCount = GetPuffMaxCount(GetPlantTier((int)SeedType::Puffshroom, cell.exp));
		cl.lastSpawnTime = board.PlayingTime;   // 避免还原后立即生成新分身
		cl.clusterAwake = false;
		g_puffClusters[cellKey] = cl;

		// 整格曾用咖啡豆唤醒 → 所有成员保持清醒（轮询帧 4.5 检测到后维持）
		if (cell.awake)
		{
			for (int i = 0; i < 5; i++)
			{
				if (cl.plants[i] == 0)
					continue;
				PVZ::Plant p(cl.plants[i]);
				if (p.isValid() && !p.NotExist)
					p.SetSleeping(false);
			}
			g_puffClusters[cellKey].clusterAwake = true;
		}
		puffCellsRestored++;
	}

	PlantExpSaveLog("[restore] OK: %d plants, exp restored to %d, puff cells restored to %d, playingTime=%d\n",
		(int)plants.size(), restored, puffCellsRestored, (int)board.PlayingTime);
	// ★ 快照保留在内存（不 clear）：若 onNewGame 随后触发会清空经验表，
	//   re-arm 后从内存重新还原；文件删除防同关重开误还原
	PlantExpSaveFinishRestore(true, "restore applied", true);
}

// 关卡开始（onBoardInitAfter）：全新关卡会话，全量重置还原状态并开始尝试。
// ★不能等 onNewGame：恢复关卡(resume)时 NewGameEvent 不触发（实测），
//   门控会无限期阻塞还原。改为：还原立即开始，onNewGame 若在还原之后触发
//   （其全量清空会冲掉已还原的经验），由 PlantExpSaveRearmAfterNewGame 从内存快照重新还原。
static void PlantExpSaveBeginLevel()
{
	g_expSaveRestorePending = true;
	g_expSaveRestoreDeadline = EXP_SAVE_RESTORE_WINDOW;
	g_expSaveSnapshotLoaded = false;
	g_expSaveSnapshotEntries.clear();
	g_expSaveSnapshotLevel.clear();
	g_expSaveAutosaveCounter = 0;
	g_expSaveDirty = false;
	g_expSaveLoggedThisLevel = false;
}

// onNewGame 之后调用：经验表刚被全量清空 → 重新挂起还原。
// 内存快照若已加载则保留（恢复流程的植物已就位，下一帧立即重新还原）；
// 未加载则等轮询帧懒加载（正常新开局 → 无文件 → 静默结束）。
static void PlantExpSaveRearmAfterNewGame()
{
	if (!g_expSaveSnapshotLoaded)
		return;   // 无快照（新开局）：无需 re-arm，懒加载路径自会处理
	// 保留 entries/level，重置消耗标记并重新挂起
	for (auto& e : g_expSaveSnapshotEntries)
		e.used = false;
	g_expSaveRestorePending = true;
	g_expSaveRestoreDeadline = EXP_SAVE_RESTORE_WINDOW;
	PlantExpSaveLog("[arm] onNewGame fired, re-arm restore from memory (entries=%d)\n",
		(int)g_expSaveSnapshotEntries.size());
}

void onNewGame()
{
	// 新游戏时清空经验数据
	g_plantExperience.clear();
	g_projectileShooterMap.clear();
	g_lastDeathRow = -1;
	g_lastDeathExp = 0;
	g_upgradeSunflowerAddr = 0;
	g_upgradeRow = -1;
	g_pendingDoubleShotPlant = 0;
	g_pendingDoubleShotCD = 0;
	g_upgradeCol = -1;
	g_upgradeExp = 0;
	// 寒冰射手状态重置
	g_snowPeaFreezeProjectiles.clear();
	g_snowPeaIcicleProjectiles.clear();
	g_icicleHitZombies.clear();
	g_speedBoostedIcicles.clear();
	g_iciclePrevX.clear();
	// 双发射手状态重置
	g_repeaterIceFireProjectiles.clear();
	g_pendingIceFireDecelerates.clear();
	// 西瓜投手状态重置（连投槽位 + 大炮弹标记）
	MelonChainResetAll();
	MelonCannonResetAll();
	// 冰西瓜状态重置（普攻计数 + 待开大队列 + 小冰瓜标记）
	IceMelonResetShots();
	// 击退弹 Pow 特效队列清空
	g_kbPowFxQCount = 0;
	// 火炬树桩状态重置
	g_projectileFireStates.clear();
	g_justFiredProjectiles.clear();
	// 裂荚射手状态重置
	g_splitPeaState.clear();
	g_spQueueHead = g_spQueueTail = g_spQueueTimer = 0;
	memset(g_spDedupPlant, 0, sizeof(g_spDedupPlant));
	memset(g_spDedupTime, 0, sizeof(g_spDedupTime));
	// 杨桃弹射状态重置
	g_starfruitState.clear();
	g_starfruitAttackCount.clear();
	g_starVolleyLimit = 5;
	// 小喷菇分身系统重置
	g_puffClusters.clear();
	g_puffToCell.clear();
	g_creatingExtraPuff = false;
	// 路灯花状态重置
	g_planternHealTimers.clear();
	// 胆小菇状态重置
	g_scaredyStates.clear();
	// 卷心菜投手散射状态重置
	CabbageClearMarks();
	g_cabbageExtraShooting = false;
	g_cabbageBounceCount = 0;
	g_cabbageNoBounce.clear();
	g_cabbageBounceArmCount = 0;
	g_bloverBoostEndTime = 0;
	g_pendingBloverTriggers.clear();
	// 经验包状态重置
	g_expPouchSelected = false;
	g_expPouchCooldownEnd = 0;
	g_drawUITopGraphics = 0;
	// 粒子特效预览器状态重置
	g_pfxPreviewActive = false;
	g_pfxPreviewIndex = 0;
	g_pfxLastSwitchCs = 0;
	g_pfxPrevF5 = g_pfxPrevF6 = g_pfxPrevF7 = 0;
	// 魅惑菇状态重置
	g_hypnoMovableZombies.clear();
	g_hypnoSelectedZombie = 0;
	g_hypnoPendingHeals.clear();
	// 剧毒体系状态重置
	g_poisonStacks.clear();
	g_poisonLastTickCs = 0;
	// 究极大喷菇状态重置（冻结值/上限/开火时刻全部清零，防跨关残留）
	UltFumeResetAll();
	UlfDebugFlush("newgame");
	// 大喷菇等阶状态重置（击退队列 + 射击间隔原值缓存，防跨关残留）
	FumeResetAll();
	// 咖啡豆唤醒解锁状态重置（新关卡所有锁定植物回到未唤醒）
	g_coffeeAwakenedPlants.clear();
	// 金盏花状态重置（形态/产出物/杀虫剂/留声机/右键沿）
	MgResetAll();
	// 墓碑吞噬者状态重置（armed 表 / 上一帧墓碑快照 / 悬浮经验包 / 选中态）
	GbResetAll();
	// 西瓜升级路线选择：复位窗口状态 + 清空待选/路线记录（不杀 reanim——旧关 reanim 已随关卡销毁）
	MelonKillChooser(0);
	MelonResetAll();
	// 冰西瓜状态重置（普攻计数 + 待开大队列）
	IceMelonResetShots();
	// 击退弹 Pow 特效队列清空
	g_kbPowFxQCount = 0;
	// 三线射手状态重置（大招/登记/标记map/双发/去重，防跨关残留）
	memset(g_tripleStates, 0, sizeof(g_tripleStates));
	g_triplePendingDir = -1;
	g_triplePendingCount = 0;
	g_tripleDblPlant = 0;
	g_tripleDblCD = 0;
	g_tripleMark.clear();
	memset(g_tripleDedupPlant, 0, sizeof(g_tripleDedupPlant));
	memset(g_tripleDedupTime, 0, sizeof(g_tripleDedupTime));
	// 机枪射手状态重置（大招槽位/pending登记/大招弹标记，防跨关残留）
	memset(g_gatlingUlt, 0, sizeof(g_gatlingUlt));
	g_gatlingPendingUlt = 0;
	g_gatlingPendingCount = 0;
	g_gatlingUltMark.clear();
	// 玉米投手状态重置（每僵尸黄油攻击计数 + pending + 缓存）
	g_cornPultHits.clear();
	g_cornFrontDist.clear();
	g_cornFrontZombie.clear();
	g_cornPendingCount = 0;
	// 坚果墙状态重置（升级回血记录，防跨关残留）
	g_wallnutCurTier.clear();
	// 高坚果状态重置（等阶/上一帧HP/累计受伤，防跨关残留）
	g_tallnutCurTier.clear();
	g_tallnutLastHp.clear();
	g_tallnutDmgAcc.clear();
	g_chomberLastState.clear();
	// 寒冰菇机制清零（爆炸登记/冻结再断言/冰法阵/脆弱集合，防跨关残留）
	g_iceBoomReqCount = 0;
	g_iceGraceCount = 0;
	g_iceFieldCount = 0;
	g_iceVulnZombies.clear();
	// 毁灭菇机制清零（爆炸登记/毁灭领域/领域内僵尸集合，防跨关残留）
	g_doomBoomReqCount = 0;
	g_doomFieldCount = 0;
	g_doomDomainZombies.clear();
	//（毒雾 2026-09-12 晚起为常驻贴图层：句柄登记在 DoomFieldRec.psys[0]，换关时游戏
	//  销毁全部粒子系统、g_doomFieldCount 清零后槽位整体作废，悬空句柄永不引用，无需逐个 Die）
	// 植物经验存档：本函数刚全量清空了经验表 → 若有内存快照则重新挂起还原
	//（onNewGame 触发晚于首次还原时，把被清掉的已还原经验补回来）
	PlantExpSaveRearmAfterNewGame();
}

void onPlantCreate(DWORD plantAddress)
{
	// 植物经验存档：布局变化（新种/恢复/补建），下一轮询帧补写快照
	g_expSaveDirty = true;

	PVZ::Plant plant(plantAddress);
	if (!plant.isValid())
		return;

	// 正在创建额外小喷菇时，不初始化集群（已在 onGameObjectsUpdate 中加入 plants 数组）
	if (g_creatingExtraPuff)
	{
		g_creatingExtraPuff = false;
		return;
	}

	// 花盆/睡莲/南瓜头没有等阶，不初始化经验（不显示 Lv/经验，也不分配经验）
	// 咖啡豆唤醒锁定的植物（保护伞等）未解锁前同样不初始化，解锁时由轮询补建
	if (!IsNoTierPlant((int)plant.Type) && IsPlantExpUnlocked(plantAddress, (int)plant.Type))
	{
		InitPlantExperience(plantAddress);
	}

	// ===== 墓碑吞噬者：继承"卡片级永久经验" =====
	// 它挖完即死、不靠击杀攒经验 ⇒ 经验只来自"队友分经验 + 肥料/经验包"，
	// 死亡时由 onPlantRemove 写回 g_gbCardExp（跨关卡），新种下时在此继承。
	// ★ 模仿者墓碑吞噬者与普通卡共用同一份卡片经验（用户已确认可接受）。
	if (plant.Type == SeedType::GraveBuster)
	{
		if (g_gbCardExp > 0)
			g_plantExperience[plantAddress] = g_gbCardExp;
		if (g_gbDebug)
			CrashStr("[GB] plant created, inherit card exp\r\n");
	}

	// 第一个小喷菇：初始化集群数据，放在 plants[0]
	if (plant.Type == SeedType::Puffshroom)
	{
		int exp = 0;
		auto expIt = g_plantExperience.find(plantAddress);
		if (expIt != g_plantExperience.end())
			exp = expIt->second;
		int tier = GetPlantTier((int)SeedType::Puffshroom, exp);
		int maxCount = GetPuffMaxCount(tier);
		int row = (int)plant.Row;
		int col = (int)plant.Column;
		int cellKey = row * 10 + col;

		PuffshroomCluster cluster;
		cluster.plants[0] = plantAddress;
		cluster.maxCount = maxCount;

		int boardAddr = MemSafeRead<int>(PVZ_BASE + 0x768);
		if (boardAddr)
			cluster.lastSpawnTime = PVZ::Board(boardAddr).PlayingTime;
		else
			cluster.lastSpawnTime = 0;

		g_puffClusters[cellKey] = cluster;
	}

	// 胆小菇：初始化渐变攻速状态（新种植物均为0阶，初速220cs）
	if (plant.Type == SeedType::Scaredyshroom)
	{
		// 必须显式初始化全部字段：栈上默认构造的 POD 成员是不确定值
		ScaredyState state;
		state.currentInterval = 220.0f;  // T0-T2 初始间隔 2.2s
		state.lastAttackTime = 0;
		state.lastManualShootTime = 0;
		state.prevShootingCD = 0;
		g_scaredyStates[plantAddress] = state;
	}
}

int onPlantReload(DWORD plantAddress, int cd)
{
	return cd;
}

// 判断方向是否为 60°（仅弹射一次，不受4/5阶"二次弹射"影响）
static bool StarIs60Dir(StarDir d)
{
	return d == SD_UR60 || d == SD_DR60;
}
// 按初始速度归类方向（游戏原生发射的5星）
static StarDir StarClassifyDir(float vx, float vy)
{
	float sp = sqrtf(vx * vx + vy * vy);
	float thresh = 0.15f * sp; // 垂直/水平判定阈值
	if (fabs(vx) < thresh)
		return (vy < 0) ? SD_UP : SD_DOWN;
	if (fabs(vy) < thresh)
		return (vx < 0) ? SD_BACK : SD_FWD;
	if (vx < 0 && vy < 0) return SD_UL45;
	if (vx < 0 && vy > 0) return SD_DL45;
	if (vx > 0 && vy < 0) return SD_UR60;
	if (vx > 0 && vy > 0) return SD_DR60;
	return SD_FWD;
}
// 注册杨桃子弹状态（3阶及以上）
// ★ 此处不读速度：事件 hook(0x45F816) 在方向设置之前触发，速度尚未写入（读到 0）。
//   方向归类/暴击改向由齐射尾 hook（0x45F874，跳转表写入速度之后）完成。
static void StarRegister(int projAddr, int tier)
{
	StarfruitState s;
	s.dir = SD_NONE;                        // 未归类（齐射尾 hook 填充）
	s.bounceIndex = 0;
	s.maxBounces = (tier >= 4) ? 2 : 1;     // 3阶1次；4/5阶2次
	g_starfruitState[projAddr] = s;
}

// 杨桃发射后的冷却调整（等阶攻速 + 向日葵光环 + 三叶草增益），每轮齐射只应用一次。
// 原 onPlantAddProjectile 中逐星执行会导致 5 次叠乘（cd*r^5），故移到齐射尾 hook 的首星处。
static void StarfruitApplyCooldown(PVZ::Plant& plant, int tier)
{
	// 等阶攻速（与通用逻辑一致：以原版豌豆 1.5s 为基准）
	{
		const float GAME_BASE_SPEED = 1.5f;
		float tierSpeed = GetPlantAttackSpeed((int)SeedType::Starfruit, tier);
		if (tierSpeed > 0)
		{
			int currentCD = plant.ShootOrProductCountdown;
			int newCD = (int)(currentCD * tierSpeed / GAME_BASE_SPEED);
			if (newCD > 0)
				plant.ShootOrProductCountdown = newCD;
		}
	}
	// 向日葵光环：同行相邻植物攻速加成
	if (g_sunflowerAuraBoost > 0.0f)
	{
		int boardAddr = MemSafeRead<int>(PVZ_BASE + 0x768);
		if (boardAddr)
		{
			PVZ::Board brd(boardAddr);
			auto allPlants = brd.GetAllPlants();
			for (auto& sf : allPlants)
			{
				if (sf.Type != SeedType::Sunflower && sf.Type != SeedType::TwinSunflower) continue;
				if ((int)sf.Row != (int)plant.Row) continue;
				if (abs((int)sf.Column - (int)plant.Column) != 1) continue;
				auto sfIt = g_plantExperience.find(sf.GetBaseAddress());
				if (sfIt == g_plantExperience.end()) continue;
				// 统一按向日葵的等阶阈值计算等阶（双子向日葵继承经验，阈价相同）
				int sfTier = GetPlantTier((int)SeedType::Sunflower, sfIt->second);
				if (sfTier >= 3)
				{
					int cd = plant.ShootOrProductCountdown;
					int newCD = (int)(cd * (1.0f - g_sunflowerAuraBoost));
					if (newCD > 0)
						plant.ShootOrProductCountdown = newCD;
					break;
				}
			}
		}
	}
	// 三叶草3阶 全屏攻速增益（冷却缩减）
	if (g_bloverBoostEndTime > 0)
	{
		int boardAddr = MemSafeRead<int>(PVZ_BASE + 0x768);
		if (boardAddr)
		{
			int nowTime = PVZ::Board(boardAddr).PlayingTime;
			if (nowTime < g_bloverBoostEndTime)
			{
				int cd = plant.ShootOrProductCountdown;
				int newCD = (int)(cd * (1.0f - g_bloverSpeedBoostReduction));
				if (newCD > 0)
					plant.ShootOrProductCountdown = newCD;
			}
			else
			{
				// 增益到期，清零结束时刻
				g_bloverBoostEndTime = 0;
			}
		}
	}
}

// ===== 齐射尾 hook 的 C++ 处理器 =====
// 每颗星"方向设置完成"后（0x45F874 循环尾）调用：edi=子弹, eax=星序号（0-4 原生 / 5-7 暴击额外）。
// 职责：①按实际速度归类方向 ②5阶暴击时右上/右下60°改45°（八向全部45°倾斜）
//       ③暴击额外星(5-7)定向：正前/左上45/左下45（原生跳转表只处理 0-4，跳过了方向设置）
//       ④首星一次性应用冷却调整（防逐星叠乘）+ 5阶暴击计数（每5次攻击一轮8星齐射）
static void __cdecl StarVolleyTailHandler(DWORD projAddr, int starIdx)
{
	// 1. 读取游戏已写入的速度（原生星 3.33）并缓存
	float vx = 0.0f, vy = 0.0f;
	{
		PVZ::Projectile p(projAddr);
		vx = p.XSpeed;
		vy = p.YSpeed;
		float sp = sqrtf(vx * vx + vy * vy);
		if (sp > 0.1f)
			g_starfruitSpeed = sp;
	}
	float spd = (g_starfruitSpeed > 0.1f) ? g_starfruitSpeed : 3.33f;

	bool isCrit = (g_starVolleyLimit == 8); // 首星计数时才置位（首星是 BACK，无需改向）
	auto it = g_starfruitState.find((int)projAddr);

	if (starIdx >= 5)
	{
		// 暴击额外星：原生 cmp eax,4; ja 跳过了方向设置 → 这里直接定向
		static const StarDir kCritExtraDir[3] = { SD_FWD, SD_UL45, SD_DL45 };
		StarDir d = kCritExtraDir[starIdx - 5];
		if (it != g_starfruitState.end())
			it->second.dir = d;
		PVZ::Projectile p(projAddr);
		p.XSpeed = STAR_DIR_VEC[d][0] * spd;
		p.YSpeed = STAR_DIR_VEC[d][1] * spd;
	}
	else if (it != g_starfruitState.end())
	{
		// 原生 5 星：按实际速度归类（此刻速度已由游戏跳转表写入）
		StarDir d = StarClassifyDir(vx, vy);
		// 5阶暴击齐射：八向全部 45° 倾斜 → 右上/右下 60° 改为 45°
		if (isCrit && d == SD_UR60)
			d = SD_UR45;
		else if (isCrit && d == SD_DR60)
			d = SD_DR45;
		it->second.dir = d;
		if (d == SD_UR45 || d == SD_DR45)
		{
			// 暴击改向的 45° 星需要重写速度（其余方向保持原生速度）
			PVZ::Projectile p(projAddr);
			p.XSpeed = STAR_DIR_VEC[d][0] * spd;
			p.YSpeed = STAR_DIR_VEC[d][1] * spd;
		}
	}

	// 3. 首星：冷却调整（一次性）+ 5阶暴击计数
	if (starIdx == 0)
	{
		DWORD shooter = 0;
		auto shIt = g_projectileShooterMap.find((int)projAddr);
		if (shIt != g_projectileShooterMap.end())
			shooter = shIt->second;
		if (shooter != 0)
		{
			PVZ::Plant plant(shooter);
			if (plant.isValid() && (int)plant.Type == (int)SeedType::Starfruit)
			{
				auto expIt = g_plantExperience.find((int)shooter);
				int exp = (expIt != g_plantExperience.end()) ? expIt->second : 0;
				int tier = GetPlantTier((int)SeedType::Starfruit, exp);
				StarfruitApplyCooldown(plant, tier);
				if (tier >= 5)
				{
					int cnt = ++g_starfruitAttackCount[(int)shooter];
					if (cnt % 5 == 0)
						g_starVolleyLimit = 8; // 本次齐射扩展为 8 星（暴击）
				}
			}
		}
	}

	// 4. 末星处理完：复位齐射上限（非暴击在 star4 复位，暴击在 star7 复位）
	if (starIdx >= g_starVolleyLimit - 1)
		g_starVolleyLimit = 5;
}

// ===== 杨桃齐射尾 hook 安装 =====
// hook @ 0x45F874（齐射循环尾，原 6 字节 = add eax,1; cmp eax,5，下一指令边界 0x45F87A）。
// trampoline:
//   pushad; push eax(星序号); push edi(子弹); call StarVolleyTailHandler; add esp,8; popad;
//   add eax,1; cmp eax,[g_starVolleyLimit]（动态上限：暴击=8 替换原 cmp eax,5）;
//   mov [esp+0x10],eax; jl 0x45F7C5（继续循环体）; jmp 0x45F884（退出循环→epilogue）
// 安装前逐字节核对运行时字节（防代码段运行时与文件不一致），不符则跳过并记日志。
static void InstallStarVolleyHook()
{
	const DWORD hookAddr = 0x45F874;
	const BYTE kExpected[6] = { 0x83, 0xC0, 0x01, 0x83, 0xF8, 0x05 }; // add eax,1; cmp eax,5

	BYTE raw[6];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 6);

	if (memcmp(raw, kExpected, 6) != 0)
	{
		return; // 不装 = 无暴击/无归类（命中时兜底归类），但绝不崩溃
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
	{
		return;
	}

	BYTE tp[64];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	// rel32 必须用 DWORD(无符号) 运算：VirtualAlloc 可能返回高地址（int 视为负数）会溢出
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                  // pushad
	tp[p++] = 0x50;                                  // push eax（星序号，第2参）
	tp[p++] = 0x57;                                  // push edi（子弹，第1参）
	putRelCall((DWORD)&StarVolleyTailHandler);       // call C++ 处理器（cdecl，调用方清栈）
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x08;  // add esp,8
	tp[p++] = 0x61;                                  // popad
	tp[p++] = 0x83; tp[p++] = 0xC0; tp[p++] = 0x01;  // add eax,1（原指令 1/2）
	// cmp eax,[g_starVolleyLimit]（动态上限替换原 cmp eax,5）
	tp[p++] = 0x3B; tp[p++] = 0x05; put32((DWORD)&g_starVolleyLimit);
	tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x10; // mov [esp+0x10],eax（原指令 3/4）
	// jl 0x45F7C5：继续循环体（下一颗星）
	tp[p++] = 0x0F; tp[p++] = 0x8C; put32((int)((DWORD)0x45F7C5 - ((DWORD)tramp + (DWORD)p + 4)));
	// 循环结束 → 跳到原函数 epilogue（pop edi; pop ebx; mov esp,ebp; pop ebp; ret）
	putRelJmp(0x45F884);

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);

	// 写 hook：5 字节 jmp + NOP 第 6 字节（原 cmp eax,5 的最后一字节 0x05，防孤立字节）
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	MemSafeWrite<BYTE>(hookAddr + 5, 0x90);

	// 写回读验证
	BYTE verify[6];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, verify, 6);
	bool ok = (memcmp(verify, hook, 5) == 0) && (verify[5] == 0x90);
}

// ===== 豌豆子弹染色标记写入（[proj+0x8C]）=====
// 0=不染色 1=弱火(淡橙黄) 2=炎(炽红) 3=冰火(冰蓝)；纯内存写，可在过火 hook 回调帧内调用
static inline void SetPeaColorMark(DWORD projAddr, int mark)
{
	MemSafeWrite<int>(projAddr + 0x8C, mark);
}

// 发射子弹事件：三线射手/玉米投手/裂荚/卷心菜/双发/寒冰 等全部等阶逻辑都在这里分发，
// 是最复杂、最容易踩到脏地址的事件回调之一（跑在游戏 hook 帧内，崩了就是游戏崩）。
// 套 __try：异常落盘后返回 1（=走原版完整发射流程），保证植物至少还能正常开火。
static int onPlantAddProjectileInner(DWORD plantAddress, DWORD projectileAddress, DWORD targetZombieAddress);

int onPlantAddProjectile(DWORD plantAddress, DWORD projectileAddress, DWORD targetZombieAddress)
{
	CRASH_STEP("onPlantAddProjectile:enter");
	__try
	{
		return onPlantAddProjectileInner(plantAddress, projectileAddress, targetZombieAddress);
	}
	__except (CrashSwallowFilter(GetExceptionInformation()))
	{
		return 1;   // 失败兜底：走原版发射流程
	}
}

static int onPlantAddProjectileInner(DWORD plantAddress, DWORD projectileAddress, DWORD targetZombieAddress)
{
	// 小喷菇非首领射击：子弹经验归首领（plants[0]）
	DWORD effectiveShooter = plantAddress;
	{
		auto pmIt = g_puffToCell.find(plantAddress);
		if (pmIt != g_puffToCell.end())
		{
			int cellKey = pmIt->second;
			auto cIt = g_puffClusters.find(cellKey);
			if (cIt != g_puffClusters.end() && cIt->second.plants[0] != 0)
				effectiveShooter = cIt->second.plants[0];
		}
	}
	// 记录子弹与发射植物的对应关系
	g_projectileShooterMap[projectileAddress] = effectiveShooter;

	// ★★ 自定义弹体标记通道清零（2026-09-11 冰西瓜两 Bug 同源根因修复）：
	//   [proj+0x8C]（小冰瓜标记200/豌豆染色1~3）与 [proj+0x78]（lastTorchCol 绘制标记，
	//   小冰瓜96/大炮95/冰锥90/雪晶91）都是模组私用通道，游戏创建弹体时不清零
	//   （PVZ.h 无 +0x8C 字段定义 = 构造函数不管它）→ 新弹继承堆残留/槽位复用残留：
	//   ① 普通冰瓜 mark≠0 → 命中判定的 "== 0" 守卫永不成立 → 冻结分支 0 执行（DIAG hit 0 条实锤）
	//   ② 小冰瓜的 200/96 残留到槽位复用的新普通冰瓜 → 被判成小冰瓜 + 画成 80% 小贴图
	//      → 观感即"散射从第 1 只开始"。
	//   本清零先于本事件内后续所有标记写入（寒冰射手91/豌豆染色/大炮95），
	//   也先于 IceMelonVolley 在 fnMelonShoot 返回后的 200/96 写入 → 互不影响。
	//   过火转火球是"已有弹体改字段"，非创建期 → 清零不影响豌豆过火。
	MemSafeWrite<int>(projectileAddress + 0x8C, 0);
	MemSafeWrite<int>(projectileAddress + 0x78, 0);

	PVZ::Plant plant(plantAddress);
	if (!plant.isValid())
		return 1;

	int seedType = (int)plant.Type;
	auto expIt = g_plantExperience.find(plantAddress);
	if (expIt == g_plantExperience.end())
		return 1;

	// ===== 连射第二发：恢复冷却值，不触发特殊效果 =====
	if (plantAddress == g_pendingDoubleShotPlant)
	{
		g_pendingDoubleShotPlant = 0;
		// 恢复第一发时计算的等阶冷却值
		if (g_pendingDoubleShotCD > 0)
			plant.ShootOrProductCountdown = g_pendingDoubleShotCD;
		g_pendingDoubleShotCD = 0;
		return 1;
	}

	int tier = GetPlantTier(seedType, expIt->second);

	// ===== 冰西瓜大招散射发射的弹：跳过攻速缩放与计数（已在大招里统一补偿冷却）=====
	if (g_iceMelonVolleyActive && seedType == (int)SeedType::WinterMelon)
		return 1;

	// ===== 卷心菜投手 散射发射的子弹：不调整攻速 =====
	// 散射循环（hook 0x464C1C）内 call 466E00 发射会触发本事件，
	// 此标志期间直接放行，避免攻速被二次缩放（散射已做冷却补偿）
	if (g_cabbageExtraShooting && seedType == (int)SeedType::Cabbagepult)
		return 1;

	// ===== 裂荚射手：子弹方向标记 + 初始X记录 =====
	// SplitPeaShoot（hook 0x464B32）已按等阶设置好攻击冷却，这里只标记左右方向。
	// ★ 事件 hook 在 0x4672B5（子弹构造 0x40D620 之后、运动类型设置前），[proj+0x58] 此刻恒为 0，
	//   方向用 g_splitPeaPendingDir 队列判定（SplitPeaShoot 发射前设置，事件同步回调读取）。
	// ★★★ 必须返回 1（不提前返回）！事件 trampoline 中 JNZ 语义：返回非 0 → 执行原 6 字节 → 继续
	//   0x466E00 完整流程；返回 0 → 跳 epilogue 提前返回。裂荚向左子弹的 [proj+0x58]=6
	//   在 0x467370 设置（0x4672CD 之后），提前返回会丢失 → 向左子弹变向右！
	// ★★★ 防崩溃：此事件运行在游戏执行流中，严禁 std::map 插入 / fopen 等 CRT 重量操作
	//   （曾致 EIP 跳指令中间崩溃）。只做纯内存写：
	//   [proj+0x80]=92/93 方向标记（炮弹专用字段，豌豆恒空；+0x78 是原生 lastTorchCol 会被过火覆写）
	//   [proj+0x84]=float 初始 X（炮弹专用字段，子弹构造时 [proj+0x30] 已是原生真实初始坐标，
	//   反弹检测用它做"确实向左飞行 ≥60px"保护，防止出生点已在左缘时误反弹）
	// ★ 攻速在 SplitPeaShoot 内设置（与 onPlantAddProjectile 同公式），下方攻速缩放排除裂荚。
	if (seedType == (int)SeedType::SplitPea)
	{
		if (g_splitPeaPendingDir == 1)
		{
			// ★ 反弹 3阶+专属（②）：低阶向左子弹标记 94（不反弹），仅用于火炬兜底/贴图镜像
			MemSafeWrite<int>(projectileAddress + 0x80,
				(tier >= 3) ? SPLIT_PEA_LEFT : SPLIT_PEA_LEFT_NB);
			float initX = MemSafeRead<float>(projectileAddress + 0x30);
			MemSafeWrite<float>(projectileAddress + 0x84, initX);
		}
		else
		{
			MemSafeWrite<int>(projectileAddress + 0x80, SPLIT_PEA_RIGHT);
		}
		// 不 return：继续走完整事件流程（含末尾 return 1），确保 0x466E00 运动类型设置完成
	}

	// ===== 三线射手：登记子弹 + 首颗攻击判定（开大/双发，v5）=====
	// ★ 普攻弹只登记 (proj, plant)，上下路判定延迟到轮询帧按 [+0x1C] 行号 vs 植物行
	//   （原版三线三颗弹出生Y几乎相同靠YSpeed漂到各行，Y差判不出；行号出生后1帧即就绪）
	// ★ 5阶双发（豌豆射手 g_pendingDoubleShot 同款）：[+0x58]=1 → 原生下一帧带射击动画
	//   自然触发第二轮完整三路；第二轮首颗在此识别恢复冷却并跳过判定（防链式）
	if (seedType == (int)SeedType::Threepeater)
	{
		int d = g_triplePendingDir;
		g_triplePendingDir = -1;

		// 大招中标记（ultTicks>0 → 本颗是大招齐射弹）
		bool inUlt = false;
		for (int k = 0; k < 24; k++)
			if (g_tripleStates[k].plant == plantAddress && g_tripleStates[k].ultTicks > 0) { inUlt = true; break; }

		if (d == TRIPLE_ULT_A || d == TRIPLE_ULT_B)
		{
			// 大招 ±θ 弹：登记（TripleUltShoot 内同步注入消费，不进轮询处理）
			if (g_triplePendingCount < 64)
			{
				g_triplePendingMarks[g_triplePendingCount].proj = projectileAddress;
				g_triplePendingMarks[g_triplePendingCount].plant = plantAddress;
				g_triplePendingMarks[g_triplePendingCount].mark = d;
				g_triplePendingMarks[g_triplePendingCount].theta = 0.0f;
				g_triplePendingCount++;
			}
		}
		else if (!inUlt)
		{
			// 普攻弹登记（轮询帧按行号打 95/96 标记）
			if (g_triplePendingCount < 64)
			{
				g_triplePendingMarks[g_triplePendingCount].proj = projectileAddress;
				g_triplePendingMarks[g_triplePendingCount].plant = plantAddress;
				g_triplePendingMarks[g_triplePendingCount].mark = 0;
				g_triplePendingMarks[g_triplePendingCount].theta = 0.0f;
				g_triplePendingCount++;
			}

			// --- 攻击判定（一轮3颗+双发第二轮都在时间窗内，只首颗生效）---
			DWORD bAddr2 = MemSafeRead<int>(plantAddress + 4);
			int nowTime = bAddr2 ? MemSafeRead<int>(bAddr2 + 0x5568) : 0;
			float tierSpeed = GetPlantAttackSpeed((int)SeedType::Threepeater, tier);
			int currentCD = MemSafeRead<int>(plantAddress + 0x58);
			if (currentCD <= 0) currentCD = 150;
			int newCD = currentCD;
			if (tierSpeed > 0)
			{
				newCD = (int)(currentCD * tierSpeed / 1.5f);
				if (newCD <= 0) newCD = 1;
			}
			int window = newCD / 2;
			if (window < 20) window = 20;
			bool first = true;
			for (int k = 0; k < 8; k++)
				if (g_tripleDedupPlant[k] == plantAddress && nowTime - g_tripleDedupTime[k] < window)
				{ first = false; break; }
			if (first)
			{
				int slot = -1, oldest = 0x7FFFFFFF;
				for (int k = 0; k < 8; k++)
				{
					if (g_tripleDedupPlant[k] == plantAddress) { slot = k; break; }
					if (g_tripleDedupTime[k] < oldest) { oldest = g_tripleDedupTime[k]; slot = k; }
				}
				g_tripleDedupPlant[slot] = plantAddress;
				g_tripleDedupTime[slot] = nowTime;

				// 5阶双发第二轮首颗：恢复等阶冷却，跳过开大/双发判定（防链式）
				if (plantAddress == g_tripleDblPlant)
				{
					g_tripleDblPlant = 0;
					MemSafeWrite<int>(plantAddress + 0x58, g_tripleDblCD);
				}
			else
			{
				// 留声机攻速加成（三线首颗弹设置冷却时再乘）
				{
					float mgf = MgBoostFactor(plantAddress);
					if (mgf < 1.0f)
						newCD = (int)(newCD * mgf);
				}
				MemSafeWrite<int>(plantAddress + 0x58, newCD);
				if (tier >= 5)
				{
					// 5阶双发：冷却=1 → 原生下一帧带动画发第二轮三路（豌豆双发同款）
					g_tripleDblPlant = plantAddress;
					g_tripleDblCD = newCD;
					MemSafeWrite<int>(plantAddress + 0x58, 1);
				}
					// ★ 开大判定（暂时禁用——大招弹平射问题未解，用户要求先注释；
					//   恢复时取消注释，并同步恢复 onGameObjectsUpdate 的三线大招状态机）
					/*
					if (tier >= 3)
					{
						int prob = (tier >= 5) ? g_threeUltProbT5 : g_threeUltProbT3;
						TripleState* st = TripleGetOrCreateState(plantAddress);
						if (prob > 0 && st && (rand() % 100) < prob)
						{
							// 开大：首轮齐射立即发出，之后每 3 tick 一轮（共 ~73 轮，约 3.7 秒）
							int plantRow2 = MemSafeRead<int>(plantAddress + 0x1C);
							st->ultTicks = 219;
							st->row = plantRow2;
							TriplePlayUltSound();
							TripleUltShoot(plantAddress, plantRow2, 219);
							TriplePlayShootSound();
						}
						else if (tier >= 5)
						{
							g_tripleDblPlant = plantAddress;
							g_tripleDblCD = newCD;
							MemSafeWrite<int>(plantAddress + 0x58, 1);
						}
					}
					*/
				}
			}
		}
		// 不 return：继续走完整事件流程（含末尾 return 1，确保 0x466E00 运动类型设置完成）
	}

	// ===== 机枪射手：大招弹登记（GatlingFrame 同步注入消费；v2 修复"大招弹统一直飞"）=====
	// 大招弹经 fnGatlingFire 原生创建同步触发本事件（发射前置 g_gatlingPendingUlt=1），
	// 此处登记 proj 地址，发射循环逐颗消费写 ±15° 速度与 ±20px 出生 Y——不依赖
	// fnGatlingFire 返回值（传 zombie=0 时返回值不可靠，v1 因此全部写入被跳过）。
	if (seedType == (int)SeedType::GatlingPea)
	{
		if (g_gatlingPendingUlt)
		{
			g_gatlingPendingUlt = 0;   // 消费标记
			if (g_gatlingPendingCount < GATLING_PENDING_SLOTS)
				g_gatlingPendingMarks[g_gatlingPendingCount++].proj = projectileAddress;
			return 1;   // 大招弹跳过通用攻速/光环块（冷却与速度由 GatlingFrame 统一管理）
		}
		// 普攻弹（hook 首颗已做等阶攻速缩放）不登记，继续走通用流程
	}

	// ===== 杨桃子弹注册（弹射机制，仅3阶及以上）=====
	// ★ 事件 hook(0x45F816) 在方向设置之前触发，此处不读速度（读到 0）——
	//   方向归类/暴击改向由齐射尾 hook(0x45F874，跳转表写入速度后)完成。
	// ★ 杨桃一轮齐射触发本事件 5 次（暴击 8 次）：攻速/光环/增益等冷却调整若逐星执行
	//   会叠乘（cd*r^5），故全部移到齐射尾 hook 的首星处一次性应用，这里直接返回。
	if (seedType == (int)SeedType::Starfruit)
	{
		if (tier >= 3)
			StarRegister((int)projectileAddress, tier);
		return 1;
	}

	// ===== 等阶攻速调整（胆小菇除外，使用自己的渐变系统；裂荚除外，攻速在 SplitPeaShoot 设置；
	// 三线射手除外，攻速在三线事件块设置——一轮齐射 3 颗弹若走此处会叠乘 3 次；
	// 玉米投手除外，攻速在玉米投手块按 2阶距离缩放；
	// 海蘑菇除外：机制规格只含剧毒（plant_attack_speed.ini 无 24 配置），
	// 保持原版攻速，不参与通用等阶缩放——scope discipline，攻速字段不改）=====
	// 游戏默认冷却值对应原版豌豆射手攻速 1.5s，以此为固定基准计算比例
	if (seedType != (int)SeedType::Scaredyshroom && seedType != (int)SeedType::SplitPea
		&& seedType != (int)SeedType::Threepeater
		&& seedType != (int)SeedType::Kernelpult
		&& seedType != (int)SeedType::Seashroom
		&& seedType != (int)SeedType::GatlingPea)   // 机枪：攻速在 0x464A34 hook 内首颗处理（一轮3~5颗弹，走这里会逐颗叠乘）
	{
		const float GAME_BASE_SPEED = 1.5f;
		// 西瓜投手卡3阶：未选路线时按 2 阶攻速（等阶解锁见"西瓜投手升级路线选择"）
		int speedTier = MelonClampTier(plantAddress, seedType, tier);
		float tierSpeed = GetPlantAttackSpeed(seedType, speedTier);
		if (tierSpeed > 0)
		{
			int currentCD = plant.ShootOrProductCountdown;
			int newCD = (int)(currentCD * tierSpeed / GAME_BASE_SPEED);
			float mgf = MgBoostFactor(plantAddress);   // 留声机攻速加成（等阶基础上再乘）
			if (mgf < 1.0f)
				newCD = (int)(newCD * mgf);
			if (newCD > 0)
				plant.ShootOrProductCountdown = newCD;
		}
	}

	// ===== 玉米投手 特殊机制（0阶原版 / 1阶黄油+5% / 2阶距离攻速 / 3阶大玉米炮）=====
	CRASH_STEP("corn:kernelpult");
	// ★ 黄油判定已迁移到攻击开始帧 hook（0x45F1E0，FindTargetAndFire 内）统一决定：
	//   原生按判定设置状态(0x3C=0x27 黄油动画)并创建相应子弹 → 动画与扔出子弹天然一致。
	//   （旧实现在此事件帧强制改子弹 Type，与原生动画状态不同步 → "显示黄油扔玉米粒" BUG）
	//   僵尸身份用轮询帧缓存的 g_cornFrontZombie（本行最靠前=索敌目标）。
	if (seedType == (int)SeedType::Kernelpult)
	{
		// 3阶: 0.5% 扔大玉米炮（改 Type=CobCannon，落地爆炸由游戏原生 DoImpact 处理）
		if (tier >= 3 && g_cornCobProbability > 0.0f
			&& (rand() % 1000) < (int)(g_cornCobProbability * 10.0f))
		{
			MemSafeWrite<int>(projectileAddress + 0x5C, (int)ProjectileType::CobCannon);
		}

		// 攻速：2阶起按索敌僵尸距离缩放（4格→1格线性缩短至 fastInterval）；
		// 低阶（0/1）走通用等阶公式（1阶的黄油机制不改变攻速）。
		// ★ 距离用轮询帧缓存的 g_cornFrontDist（本行最靠前僵尸），事件帧不做重扫描。
		{
			float tierSpeed = GetPlantAttackSpeed((int)SeedType::Kernelpult, tier);
			if (tierSpeed > 0)
			{
				int currentCD = plant.ShootOrProductCountdown;
				int baseCD = (int)(currentCD * tierSpeed / 1.5f);   // 通用等阶基准
				if (baseCD <= 0) baseCD = 1;
				int newCD = baseCD;
				if (tier >= 2)
				{
					float dist = -1.0f;
					auto dit = g_cornFrontDist.find(plantAddress);
					if (dit != g_cornFrontDist.end()) dist = dit->second;
					if (dist >= 1.0f)
					{
						if (dist < 1.0f) dist = 1.0f;
						if (dist > 4.0f) dist = 4.0f;
						newCD = (int)((float)g_cornFastIntervalCs
							+ (float)(baseCD - g_cornFastIntervalCs) * (dist - 1.0f) / 3.0f);
						if (newCD <= 0) newCD = 1;
					}
					// dist < 1（无僵尸/未缓存）→ 保持 baseCD，不做距离加速
				}
				float mgf = MgBoostFactor(plantAddress);   // 留声机攻速加成
				if (mgf < 1.0f)
					newCD = (int)(newCD * mgf);
				if (newCD > 0)
					plant.ShootOrProductCountdown = newCD;
			}
		}
	}

	// ===== 西瓜投手 特殊机制（T3连投 / T4最多5连 / T5西瓜大炮标记）=====
	// 连投实现与豌豆射手连射同款：[+0x58]=1 → 游戏下一帧原生补发（带投掷动画），
	// 补发触发的本事件里继续判定/收尾（恢复首发保存的等阶冷却）。
	// ★ 此处 tier 已经过等阶攻速缩放块，CD 是缩放后的值——savedCD 保存的正是它。
	// ★ 卡3阶未选路线（MelonClampTier 压回 2）不触发任何机制。
	CRASH_STEP("melon:melonpult");
	if (seedType == (int)SeedType::Melonpult)
	{
		int mechTier = MelonClampTier(plantAddress, seedType, tier);
		MelonChain* ch = MelonChainFind(plantAddress);
		if (ch)
		{
			// 本轮第 2~N 发：4阶起继续判定连投（每发独立 roll，最多 5 连）
			ch->count++;
			bool keep = (mechTier >= 4 && ch->count < 5
				&& g_melonChainProbability > 0.0f
				&& (rand() % 1000) < (int)(g_melonChainProbability * 10.0f));
			if (keep)
			{
				plant.ShootOrProductCountdown = 1;   // 下一帧继续连投
			}
			else
			{
				// 连投结束：恢复首发保存的等阶冷却（后续光环/增益块会在此之上再调整）
				if (ch->savedCD > 0)
					plant.ShootOrProductCountdown = ch->savedCD;
				MelonChainFree(ch);
				// 本发即本轮最后一发 → 5阶西瓜大炮
				if (mechTier >= 5)
					MelonCannonMark(projectileAddress, plantAddress);
			}
		}
		else
		{
			// 本轮第一发：3阶起判定连投
			bool chain = (mechTier >= 3 && g_melonChainProbability > 0.0f
				&& (rand() % 1000) < (int)(g_melonChainProbability * 10.0f));
			if (chain && (ch = MelonChainAlloc(plantAddress)) != 0)
			{
				ch->count = 1;
				ch->savedCD = plant.ShootOrProductCountdown;   // 已是等阶调整后的冷却
				plant.ShootOrProductCountdown = 1;             // 下一帧原生补发第二发
			}
			else if (mechTier >= 5)
			{
				// 无连投（或槽位满退化）：本轮唯一一发即最后一发 → 西瓜大炮
				MelonCannonMark(projectileAddress, plantAddress);
			}
		}
	}

	// ===== 冰西瓜 特殊机制（T4命中冻结 / T5每5次普攻大招散射）=====
	// 冰西瓜由西瓜投手选路线B 替换而来（保留经验/等阶），此处只做：
	//   ① 5阶普攻计数：每满 ICE_MELON_VOLLEY_PERIOD 次 → 登记"待开大"（POD 队列）
	//      实际发射在下一帧轮询帧（IceMelonVolleyFrame）执行，避开本事件帧的 CRT 禁忌
	//   ② 4阶命中冻结：在 onProjectileHitZombie 按来源植物+等阶判定（本事件不管命中）
	// ★ 本事件帧禁 std::map 插入 → 计数用 POD 数组 g_iceMelonShots，登记用 POD 队列
	CRASH_STEP("icemelon:shot");
	if (seedType == (int)SeedType::WinterMelon)
	{
		// 大招散射发射产生的弹：不重复计数（g_iceMelonVolleyActive 只在发射帧置位，
		// 但 0x466E00 发射同步回调本事件 → 用标志短路）
		if (!g_iceMelonVolleyActive)
		{
			int slot = IceMelonFindShot(plantAddress);
			if (slot < 0)
			{
				for (int i = 0; i < 32; i++)
					if (g_iceMelonShots[i].plant == 0) { slot = i; break; }
				if (slot >= 0) { g_iceMelonShots[slot].plant = plantAddress; g_iceMelonShots[slot].count = 0; }
			}
			if (slot >= 0)
			{
				g_iceMelonShots[slot].count++;
				if (tier >= 5 && g_iceMelonShots[slot].count >= ICE_MELON_VOLLEY_PERIOD)
				{
					g_iceMelonShots[slot].count = 0;
					// 登记待开大（槽满则弃，不阻断普攻）
					if (g_iceMelonVolleyQCount < 8)
						g_iceMelonVolleyQ[g_iceMelonVolleyQCount++] = plantAddress;
				}
			}
		}
	}

	// ===== 胆小菇渐变攻速 =====
	if (seedType == (int)SeedType::Scaredyshroom)
	{
		float initialInterval = (tier >= 3) ? 150.0f : 220.0f;  // T3+初速1.5s, T0-T2初速2.2s
		float minInterval = GetPlantAttackSpeed(seedType, tier) * 100.0f;  // 秒→厘秒

		auto& state = g_scaredyStates[plantAddress];
		if (state.currentInterval <= 0.0f)
		{
			state.currentInterval = initialInterval;
			state.lastAttackTime = 0;
		}

		// 累计不攻击时间 → 间隔延长（每1秒 +speedUp cs）
		// ★ 关键：只计算超出冷却期的空闲，冷却期内不算"不攻击"
		//    否则连续射击时冷却期200+cs的加速(4+cs)会完全抵消减速(2cs)
		int boardAddr = MemSafeRead<int>(PVZ_BASE + 0x768);
		int nowTime = boardAddr ? PVZ::Board(boardAddr).PlayingTime : 0;
		if (state.lastAttackTime > 0 && nowTime > state.lastAttackTime)
		{
			int totalIdle = nowTime - state.lastAttackTime;
			int expectedCD = (int)(state.currentInterval + 0.5f); // 上次设定的冷却
			float excessIdle = (float)(totalIdle - expectedCD);    // 超出冷却的才是真空闲
			if (excessIdle > 0.0f)
			{
				float speedUp = excessIdle * (g_scaredySpeedUpMs / 10.0f) / 100.0f;  // ms→cs
				state.currentInterval += speedUp;
				if (state.currentInterval > initialInterval)
					state.currentInterval = initialInterval;
			}
		}

		// 本次攻击 → 间隔缩短（每发 -speedDown cs）
		state.currentInterval -= (float)g_scaredySpeedDownMs / 10.0f;  // ms→cs
		if (state.currentInterval < minInterval)
			state.currentInterval = minInterval;

		// 应用实际间隔
		plant.ShootOrProductCountdown = (int)(state.currentInterval + 0.5f);
		plant.ShootOrProductInterval = (int)(state.currentInterval + 0.5f);
		// 留声机攻速加成（胆小菇渐变间隔基础上再乘）
		{
			float mgf = MgBoostFactor(plantAddress);
			if (mgf < 1.0f)
			{
				plant.ShootOrProductCountdown = (int)(plant.ShootOrProductCountdown * mgf);
				plant.ShootOrProductInterval = (int)(plant.ShootOrProductInterval * mgf);
			}
		}
		state.lastAttackTime = nowTime;
	}

	// 攻击速度调整已完成，冷却值 nowCD 是等阶调整后的值

	// ===== 连射的第二个子弹不触发特殊效果 =====
	// (由上面的 plantAddress == g_pendingDoubleShotPlant 处理)

	// ===== 向日葵/双子向日葵光环：同行相邻植物攻速加成 =====
	if (g_sunflowerAuraBoost > 0.0f && seedType != (int)SeedType::Sunflower && seedType != (int)SeedType::TwinSunflower)
	{
		int boardAddr = MemSafeRead<int>(PVZ_BASE + 0x768);
		if (boardAddr)
		{
			PVZ::Board brd(boardAddr);
			auto allPlants = brd.GetAllPlants();
			for (auto& sf : allPlants)
			{
				if (sf.Type != SeedType::Sunflower && sf.Type != SeedType::TwinSunflower) continue;
				if ((int)sf.Row != (int)plant.Row) continue;
				if (abs((int)sf.Column - (int)plant.Column) != 1) continue;
				auto sfIt = g_plantExperience.find(sf.GetBaseAddress());
				if (sfIt == g_plantExperience.end()) continue;
				// 统一按向日葵的等阶阈值计算等阶（双子向日葵继承经验，阈价相同）
				int sfTier = GetPlantTier((int)SeedType::Sunflower, sfIt->second);
				if (sfTier >= 3)
				{
					int cd = plant.ShootOrProductCountdown;
					int newCD = (int)(cd * (1.0f - g_sunflowerAuraBoost));
					if (newCD > 0)
						plant.ShootOrProductCountdown = newCD;
					break;
				}
			}
		}
	}

	// ===== 三叶草3阶 全屏攻速增益（冷却缩减，不含卡槽冷却）=====
	// 增益期间所有植物的攻击/生产冷却再缩减 g_bloverSpeedBoostReduction
	if (g_bloverBoostEndTime > 0)
	{
		int boardAddr = MemSafeRead<int>(PVZ_BASE + 0x768);
		if (boardAddr)
		{
			int nowTime = PVZ::Board(boardAddr).PlayingTime;
			if (nowTime < g_bloverBoostEndTime)
			{
				int cd = plant.ShootOrProductCountdown;
				int newCD = (int)(cd * (1.0f - g_bloverSpeedBoostReduction));
				if (newCD > 0)
					plant.ShootOrProductCountdown = newCD;
			}
			else
			{
				// 增益到期，清零结束时刻
				g_bloverBoostEndTime = 0;
			}
		}
	}

	// ===== 3阶+ 击退子弹（豌豆射手专属） =====
	if (seedType == (int)SeedType::Peashooter && tier >= 3 && (rand() % 100) < g_knockbackProbability)
	{
		g_knockbackProjectiles.insert(projectileAddress);
		// 子弹速度提升 2 倍
		PVZ::Projectile projectile(projectileAddress);
		projectile.XSpeed = projectile.XSpeed * 2.0f;
		// 击退弹标记 [proj+0x78]=97，绘制 hook @ 0x46E6C7 据此替换贴图
		// （同冰锥90/雪晶91 通道；若过火炬会被原生 OnFire 覆写为火豆，属自然行为）
		MemSafeWrite<int>(projectileAddress + 0x78, 97);
	}

	// ===== 5阶 连射（豌豆射手专属） =====
	// 不直接调用 Shoot()（会递归破坏游戏内部状态导致崩溃），
	// 改为将冷却设为 1 帧，让游戏更新循环自然触发第二发
	if (seedType == (int)SeedType::Peashooter && tier >= 5 && (rand() % 100) < g_doubleShotProbability)
	{
		g_pendingDoubleShotPlant = plantAddress;
		g_pendingDoubleShotCD = plant.ShootOrProductCountdown; // 保存等阶冷却值
		plant.ShootOrProductCountdown = 1;                     // 下一帧立即触发第二发
	}

	// ===== 寒冰射手 三/四阶 冻结 =====
	// 子弹有概率冻结僵尸2s（寒冰菇冻结效果）
	if (seedType == (int)SeedType::SnowPea && tier >= 3 && tier <= 4)
	{
		if ((rand() % 100) < g_snowPeaFreezeProbability)
		{
			g_snowPeaFreezeProjectiles.insert(projectileAddress);
			// 雪晶标记 [proj+0x78]=91，绘制 hook @ 0x46E6C7 据此替换贴图
			MemSafeWrite<int>(projectileAddress + 0x78, 91);
		}
	}

	// ===== 寒冰射手 五阶 冰锥 =====
	// 取消三/四阶机制，改为概率射出冰锥：速度1.5倍、伤害40无视二类防具、穿透、减速/冻结
	if (seedType == (int)SeedType::SnowPea && tier >= 5)
	{
		if ((rand() % 100) < g_snowPeaIcicleProbability)
		{
			g_snowPeaIcicleProjectiles.insert(projectileAddress);
			g_icicleHitZombies[projectileAddress] = std::set<int>();
			// 冰锥标记 [proj+0x78]=90，绘制 hook @ 0x46E6C7 据此替换贴图
			MemSafeWrite<int>(projectileAddress + 0x78, 90);
			// 加速在 onGameObjectsUpdate 中测量移动距离补 50%（[3C]速度字段创建时为0不可用）
		}
	}

	// ===== 双发射手 特殊机制 =====
	// 2阶：20%概率射出冰豌豆（Type=SnowPea，行为生效但贴图暂为普通豌豆）
	// 3阶：保留2阶 + 20%概率射出火豌豆（OnFire()：贴图+伤害+溅射正确）
	// 5阶：保留2阶、3阶 + 20%概率射出冰火豌豆（OnFire()贴图+溅射，减速延迟到下一帧）
	// 各概率独立，优先级：冰火 > 火 > 冰 > 普通
	if (seedType == (int)SeedType::Repeater && tier >= 2)
	{
		int roll = rand() % 100;
		PVZ::Projectile projectile(projectileAddress);

		if (tier >= 5 && roll < g_repeaterIceFirePeaProbability)
		{
			// 5阶冰火豌豆：OnFire()处理贴图+伤害+溅射，减速延迟到onGameObjectsUpdate
			projectile.OnFire();
			g_repeaterIceFireProjectiles.insert(projectileAddress);
			// 染色标记：冰火(3)=冰蓝（[proj+0x8C]）
			SetPeaColorMark(projectileAddress, 3);
		}
		else if (tier >= 3 && roll < g_repeaterIceFirePeaProbability + g_repeaterFirePeaProbability)
		{
			// 3阶+ 火豌豆：OnFire()同时处理Type+贴图
			projectile.OnFire();
		}
		else if (roll < g_repeaterIceFirePeaProbability + g_repeaterFirePeaProbability + g_repeaterIcePeaProbability)
		{
			// 2阶+ 冰豌豆：改Type=SnowPea，减速行为生效，贴图暂为普通豌豆
			projectile.Type = ProjectileType::SnowPea;
		}
		// else: 普通豌豆，不做任何修改
	}

	return 1;
}

void onPlantRemove(DWORD plantAddress)
{
	// ===== 植物死亡经验转移 =====
	// PlantDieEvent(0x4679B9) hook
	//
	// ★ 铁律：pushad/popad 包裹，栈变量传递，禁止写全局变量和调 ReadMemory
	int saveRow = -1;
	int saveExp = 0;
	int puffCellKey = -1;        // 小喷菇所属格子key（-1=不是小喷菇）
	int gbCardExpOut = -1;       // 墓碑吞噬者：待写回的"卡片级永久经验"（-1=不是墓碑吞噬者）

	__asm pushad

	// ===== 小喷菇检测：属于哪个格子 =====
	{
		auto puffIt = g_puffToCell.find(plantAddress);
		if (puffIt != g_puffToCell.end())
		{
			puffCellKey = puffIt->second;
		}
		else
		{
			// 不在 g_puffToCell 中，检查是否是 leader（plants[0]）
			for (auto& pair : g_puffClusters)
			{
				if (pair.second.plants[0] == plantAddress)
				{
					puffCellKey = pair.first;
					break;
				}
			}
		}
	}

	auto it = g_plantExperience.find(plantAddress);
	if (it != g_plantExperience.end())
	{
		int exp = it->second;
		if (exp > 0)
		{
			// 花盆/睡莲/南瓜头没有等阶：死亡时经验不分发给同行
			int dieSeedType = -1;
			__asm {
				mov eax, plantAddress
				mov eax, [eax + 0x24]
				mov dieSeedType, eax
			}
			if (!IsNoTierPlant(dieSeedType))
			{
				// ★ 墓碑吞噬者（2026-10-21 定案）：其经验**不分配给同行**，
				//   而是写回"卡片级永久经验"（本例经验 = 卡上继承值 + 本次存活期间新增），
				//   下次种下墓碑吞噬者时由 onPlantCreate 继承。
				if (dieSeedType == (int)SeedType::GraveBuster)
				{
					gbCardExpOut = exp;
				}
				else
				{
					int row = -1;
					__asm {
						mov eax, plantAddress
						mov eax, [eax + 0x1C]
						mov row, eax
					}
					if (row >= 0 && row <= 5)
					{
						// 机枪（v2 扣整万方案）：exp 本身含未消耗的大招进度（可超 limit），
						// 死亡时全额均分给同行，进度随之自动转移——无需再查能量流水
						saveRow = row;
						saveExp = exp;
					}
				}
			}
		}
	}
	RemovePlantExperience(plantAddress);

	__asm popad

	// ===== 墓碑吞噬者：卡片级永久经验回写（真正落盘在轮询帧 GbFrame）=====
	// ★ 只增不减：实例经验正常 = 卡片继承值 + 本关新增，所以必然 >= 当前卡片值。
	//   加这层保护是为了防止任何"异常清零实例经验"的路径把卡片养成成果洗掉。
	if (gbCardExpOut >= 0 && gbCardExpOut > g_gbCardExp)
		g_gbCardSavePending = gbCardExpOut;   // hook 帧只写 POD，绝不 fopen

	// ===== 樱桃炸弹/火爆辣椒等阶爆炸机制 =====
	// 灰烬植物走 Effect 爆炸路径，不经过 PlantDamageZombieEvent hook。
	// 改用 onPlantRemove(PlantDieEvent) 拦截，必定触发。
	// 直接读 plant+0x24/0x1C/0x28 内存，避免 PVZ::Plant 包装器失效。
	// ★化灰定案（2026-09-11，反汇编 0x41D8A0/0x532B70 实证）：击杀改走 z.Blast()
	//   （原版 ApplyBurn 路径，与原版樱桃/辣椒化灰视觉完全一致），替代 HitBody
	//   （HitBody 击杀=掉头动画，与灰烬植物身份不符）。
	//   ★T2/T3 伤害加成(2400/3600)保留：ashKill 先对幸存巨人 HitBody(dmg-1800) 压血，
	//   再 Blast 化灰收尾（见 ashKill 内注释）；普通僵尸仍纯化灰。
	{
		int bombTier = -1;
		SeedType::SeedType bombType = SeedType::Peashooter;
		int bombRow = -1, bombCol = -1;

		int rawType = MemSafeRead<int>(plantAddress + 0x24);
		if (rawType == (int)SeedType::CherryBomb || rawType == (int)SeedType::Jalapeno)
		{
			bombType = (SeedType::SeedType)rawType;
			bombRow = MemSafeRead<int>(plantAddress + 0x1C);
			bombCol = MemSafeRead<int>(plantAddress + 0x28);
			bombTier = GetPlantTier(rawType, saveExp);
		}

		if (bombTier >= 1)
		{
			int dmg = 1800;
			if (bombTier >= 3)      dmg = 3600;
			else if (bombTier >= 2) dmg = 2400;

			// 化灰 + 溢出伤害两全（2026-09-11）：ApplyBurn 对本体 HP≥1800 的僵尸只烧 1800 不死，
			// T2/T3 伤害加成(2400/3600)若只靠 Blast 会丢失。方案 = 先压血后化灰：
			//   仅对本体能从灰烬中幸存的僵尸（本体 HP≥1800，即巨人类）先 HitBody(dmg-1800) 补溢出——
			//   补伤后 HP 若压到 1800 以下，随后的 Blast() 恰好以化灰动画收尾（总伤害=dmg 全额）；
			//   普通僵尸（HP<1800）跳过补伤直接 Blast 化灰，绝不走 HitBody 击杀（避免掉头动画）。
			auto ashKill = [&](PVZ::Zombie& zombie, int killDmg)
			{
				DWORD zAddr = zombie.GetBaseAddress();
				MemSafeWrite<int>(zAddr + 0x148, plantAddress);
				if (killDmg > 1800)
				{
					int hp = MemSafeRead<int>(zAddr + 0xC8);
					if (hp >= 1800)
						zombie.HitBody(killDmg - 1800);
				}
				zombie.Blast();
			};

			int pvzBase = MemSafeRead<int>(0x6A9EC0);
			if (pvzBase >= 0x400000)
			{
				int boardAddr = MemSafeRead<int>(pvzBase + 0x768);
				if (boardAddr)
				{
					PVZ::Board board(boardAddr);
					auto zombies = board.GetAllZombies();

					if (bombType == SeedType::CherryBomb)
					{
						int centerX = board.GridToXPixel(bombRow, bombCol);
						int centerY = board.GridToYPixel(bombRow, bombCol);
						int radiusSq = 180 * 180;

						for (auto& zombie : zombies)
						{
							if (!zombie.isValid() || zombie.NotExist) continue;
							int dx = (int)zombie.X - centerX;
							int dy = (int)zombie.Y - centerY;
						if (dx * dx + dy * dy <= radiusSq)
						{
							ashKill(zombie, dmg);   // 化灰死亡 + T2/T3 溢出补伤
						}
						}
					}
					else // Jalapeno
					{
						for (auto& zombie : zombies)
						{
							if (!zombie.isValid() || zombie.NotExist) continue;

							// 像素范围匹配——避免整数除法边界偏差
							// GridToXPixel(col) = 80*col+40, 列宽80px
							int centerX = board.GridToXPixel(bombRow, bombCol);
							int centerY = board.GridToYPixel(bombRow, bombCol);
							bool sameRow = (zombie.Y >= centerY - 45 && zombie.Y < centerY + 45);
							bool sameCol = (zombie.X >= centerX - 40 && zombie.X < centerX + 40);

							if (sameRow || sameCol)
							{
								ashKill(zombie, dmg);   // 化灰死亡 + T2/T3 溢出补伤
							}
						}

						// T1: 本列格子创建火焰动画（游戏只处理本行火焰，列需手动）
						// 先注释火焰创建——在 onPlantRemove 上下文中调用 CreateReanimation 可能崩溃
						// 待定位崩溃后重新启用
						/*
						{
							int maxRows = 5;
							if (board.GetBaseAddress())
							{
								int sceneType = MemSafeRead<int>(pvzBase + 0x554C);
								if (sceneType == 2 || sceneType == 3)
									maxRows = 6;
							}

							for (int r = 0; r < maxRows; r++)
							{
								if (r == bombRow) continue;
								float fx = (float)board.GridToXPixel(r, bombCol);
								float fy = (float)board.GridToYPixel(r, bombCol);
								Creator::CreateReanimation(AnimationType::Flame, fx, fy);
							}
						}
						*/
					}
				}
			}
		}
	}

	// ===== 寒冰菇爆炸：登记延迟执行请求（冻结/伤害/冰法阵轮询帧处理）=====
	//   事件帧只写 POD 队列，绝不在这里调 Froze/HitBody/CreateEffect（防崩溃铁律）；
	//   实际冻结+伤害+法阵由 onGameObjectsUpdate 里的 IceFieldFrame 轮询消费。
	//   等阶用死亡前 saveExp 判定 GetPlantTier（配置已封顶 3 阶）。
	{
		int itype = MemSafeRead<int>(plantAddress + 0x24);
		if (itype == (int)SeedType::Iceshroom)
		{
			int irow = MemSafeRead<int>(plantAddress + 0x1C);
			int icol = MemSafeRead<int>(plantAddress + 0x28);
			if (irow >= 0 && irow <= 5 && icol >= 0 && icol <= 8 && g_iceBoomReqCount < 16)
			{
				g_iceBoomReqs[g_iceBoomReqCount].row = irow;
				g_iceBoomReqs[g_iceBoomReqCount].col = icol;
				g_iceBoomReqs[g_iceBoomReqCount].tier = GetPlantTier((int)SeedType::Iceshroom, saveExp);
				g_iceBoomReqCount++;
			}
		}
	}

	// ===== 毁灭菇爆炸：登记延迟执行请求（化灰爆炸/毁灭领域轮询帧处理）=====
	//   事件帧只写 POD 队列（防崩溃铁律），实际化灰 + 领域由 DoomFieldFrame 轮询消费。
	//   等阶用死亡前 saveExp 判定（此时经验记录已移除）。
	{
		int itype = MemSafeRead<int>(plantAddress + 0x24);
		if (itype == (int)SeedType::Doomshroom)
		{
			int irow = MemSafeRead<int>(plantAddress + 0x1C);
			int icol = MemSafeRead<int>(plantAddress + 0x28);
			if (irow >= 0 && irow <= 5 && icol >= 0 && icol <= 8 && g_doomBoomReqCount < 8)
			{
				g_doomBoomReqs[g_doomBoomReqCount].row = irow;
				g_doomBoomReqs[g_doomBoomReqCount].col = icol;
				g_doomBoomReqs[g_doomBoomReqCount].tier = GetPlantTier((int)SeedType::Doomshroom, saveExp);
				g_doomBoomReqCount++;
			}
		}
	}

	// 坚果墙移除：清空其等阶记录（防内存池地址复用误判）
	g_wallnutCurTier.erase(plantAddress);
	// 高坚果移除：清空其等阶/受伤记录（防内存池地址复用误判）
	g_tallnutCurTier.erase(plantAddress);
	g_tallnutLastHp.erase(plantAddress);
	g_tallnutDmgAcc.erase(plantAddress);
	// 大嘴花移除：清空其消化状态（防内存池地址复用误判回血）
	g_chomberLastState.erase(plantAddress);

	// ===== 小喷菇清理：从集群移除，不连坐（在 popad 之后写全局变量）=====
	if (puffCellKey >= 0)
	{
		g_puffToCell.erase(plantAddress);
		auto clusterIt = g_puffClusters.find(puffCellKey);
		if (clusterIt != g_puffClusters.end())
		{
			clusterIt->second.RemovePlant(plantAddress);
		}
	}

	// ===== 胆小菇清理：移除渐变攻速状态 =====
	g_scaredyStates.erase(plantAddress);

	// ===== 裂荚射手清理：移除 5阶 状态 =====
	g_splitPeaState.erase(plantAddress);

	// 经验分配（onGameObjectsUpdate 会拦截首领死的经验，提拔后继者时转移经验）
	if (saveRow >= 0)
	{
		g_lastDeathRow = saveRow;
		g_lastDeathExp = saveExp;
	}

	// ===== 金盏花清理：移除该株的产出物/留声机加成/杀虫剂区域/形态记录 =====
	MgCleanupPlant(plantAddress);

	// 植物经验存档：布局变化（死亡/铲除），下一轮询帧补写快照
	g_expSaveDirty = true;
}

// ===== 火炬树桩 查找同行火炬等阶（子弹过火时调用）=====
// 返回同行火炬最高等阶；无火炬返回 -1；outCol 输出火炬列号
static int FindTorchwoodTierForProjectile(DWORD projectileAddress, int* outCol)
{
	if (outCol) *outCol = -1;
	PVZ::Projectile projectile(projectileAddress);
	if (!projectile.isValid() || projectile.NotExist) return -1;

	int projRow = (int)projectile.Row;
	float projectileX = projectile.X;

	int boardAddr = MemSafeRead<int>(PVZ_BASE + 0x768);
	if (!boardAddr) return -1;
	PVZ::Board board(boardAddr);
	if (!board.GetBaseAddress()) return -1;

	int bestTier = -1;
	int bestCol = -1;
	auto allPlants = board.GetAllPlants();
	for (auto& plant : allPlants)
	{
		if (plant.Type != SeedType::Torchwood) continue;
		if ((int)plant.Row != projRow) continue;
		if (plant.NotExist) continue;

		int plantAddr = plant.GetBaseAddress();
		auto expIt = g_plantExperience.find(plantAddr);
		int tier = 0;
		if (expIt != g_plantExperience.end())
			tier = GetPlantTier((int)SeedType::Torchwood, expIt->second);

		float torchX = (float)board.GridToXPixel(projRow, (int)plant.Column) + 40.0f;
		if (projectileX >= torchX - 30.0f && projectileX <= torchX + 50.0f)
		{
			if (tier > bestTier)
			{
				bestTier = tier;
				bestCol = (int)plant.Column;
			}
		}
	}
	if (bestTier >= 0 && outCol) *outCol = bestCol;
	return bestTier;
}

// ===== 火炬树桩 普通豌豆过火（hook @ 0x4606B7 trampoline 调用）=====
// 游戏原生流程：0x460610 子弹碰撞检测（只处理 Type 0/1），Type==0 时在 0x4606B7
// 调用 OnFire(0x46ECB0)（Type→6 FirePea + 火球贴图/音效/粒子）。
// 我们在 trampoline 里先记录自定义过火状态，随后执行原生 OnFire（弱火豌豆
// 贴图暂用原生火豌豆）。FirePea(6) 在类型检查时被原生跳过 → "火豌豆过火不受影响"。
// 等阶机制：
//   0阶: 普通豌豆→弱火豌豆(30)，贴图用火豌豆（原生 OnFire）
//   1阶: 同0阶（弱火30）
//   2阶+: 普通豌豆→火豌豆(40，4阶50)
//   5阶: 不消除僵尸减速/冻结
// 找不到火炬（其它 OnFire 调用源，防御）→ 不干预，原生 OnFire 正常执行。
void onPeaOnFire(DWORD projectileAddress)
{
	PVZ::Projectile projectile(projectileAddress);
	if (!projectile.isValid() || projectile.NotExist)
		return;
	if ((int)projectile.Type != (int)ProjectileType::Pea)
		return;

	// 本帧已被处理过（onSnowPeaFire 冰火豆等），跳过防重复
	if (g_justFiredProjectiles.find(projectileAddress) != g_justFiredProjectiles.end())
		return;

	// 找到同行火炬树桩判等阶
	int torchCol = -1;
	int tier = FindTorchwoodTierForProjectile(projectileAddress, &torchCol);
	if (tier < 0)
		return;   // 无火炬：原生 OnFire 执行（默认火豌豆，伤害40+溅射）

	ProjectileFireState newState;
	newState.fireLevel = (tier >= 2) ? 2 : 1;   // 0-1阶弱火(1)，2阶+直接火(2)
	newState.damage = (tier >= 2) ? ((tier >= 4) ? 50 : 40) : 30;
	newState.noDefrost = (tier >= 5);
	newState.lastTorchCol = torchCol;
	g_projectileFireStates[projectileAddress] = newState;
	g_justFiredProjectiles.insert(projectileAddress);
	// 豌豆染色标记：弱火(1)=淡橙黄，火(2)=不染色保持原版火球（[proj+0x8C]，绘制 hook @ 0x46E805 读取）
	SetPeaColorMark(projectileAddress, (newState.fireLevel == 1) ? 1 : 0);
	// 原生 OnFire() 随后由 trampoline 执行：Type→FirePea(6) + 火球贴图
	// 自定义伤害在 onProjectileHitZombie 中覆盖（30/40/50/60/80）
}

// ===== 火炬树桩 冰豌豆过火（hook @ 0x4606CB trampoline 调用）=====
// 游戏原生流程：Type==1(SnowPea) 时在 0x4606CB 调用 0x46EE00（Type→0 普通豌豆，
// 冰消——"冰豌豆过火变成普通豌豆"的原版实现）。
// 返回 0 = 走原生 0x46EE00（0阶火炬：冰豌豆→普通豌豆，同原版）
// 返回 1 = 已处理（1阶+火炬：冰火豆，同双发射手 5 阶：OnFire 火球贴图 + 火伤害
//          40/50 + 溅射 + defrost，命中后延迟一帧上减速）
int onSnowPeaFire(DWORD projectileAddress)
{
	PVZ::Projectile projectile(projectileAddress);
	if (!projectile.isValid() || projectile.NotExist) return 0;
	if ((int)projectile.Type != (int)ProjectileType::SnowPea) return 0;

	int torchCol = -1;
	int tier = FindTorchwoodTierForProjectile(projectileAddress, &torchCol);
	if (tier < 1)
		return 0;   // 无火炬或0阶：原生 0x46EE00 变普通豌豆

	// 1阶+：冰火豆
	// 1) 预写 [proj+0x78] 非零 + 显式设 EAX，确保 OnFire 入口的
	//    cmp [edi+0x78], eax 不相等（否则 OnFire 直接返回，Type 不变）
	MemSafeWrite<int>(projectileAddress + 0x78, 0x5A);
	__asm {
		mov ecx, projectileAddress
		mov eax, 0x5A5A5A5A
		mov ebx, 0x46ECB0
		call ebx          // 原生 OnFire：Type→FirePea(6) + 火球贴图/音效/粒子
	}
	// 2) 记录自定义伤害状态（命中时覆盖，防止原生 FirePea 40 双伤）
	ProjectileFireState fs;
	fs.fireLevel = 2;
	fs.damage = (tier >= 4) ? 50 : 40;
	fs.noDefrost = (tier >= 5);
	fs.lastTorchCol = torchCol;
	g_projectileFireStates[projectileAddress] = fs;
	// 3) 冰火豆标记：命中时记录延迟减速（先让火 defrost 完成，下一帧再上减速）
	g_repeaterIceFireProjectiles.insert(projectileAddress);
	g_justFiredProjectiles.insert(projectileAddress);
	// 染色标记：冰火(3)=冰蓝（[proj+0x8C]）
	SetPeaColorMark(projectileAddress, 3);
	return 1;
}

// ===== 火炬树桩过火 hook 安装 =====
// hook @ 0x4606B7（普通豌豆过火，原 call 0x46ECB0，5字节 E8）
// hook @ 0x4606CB（冰豌豆过火，原 call 0x46EE00，5字节 E8）
// 两个 trampoline 都只做"类型判定 + 调 C++"，逻辑全在 C++，
// 避免在汇编里做复杂操作（见 pvz-projectile-custom 技能踩坑结论）。
// 安装延迟到 onGameObjectsUpdate 首次执行（游戏代码解密完成后）。
static void InstallTorchwoodHooks()
{
	// ---- Hook A @ 0x4606B7（普通豌豆过火）----
	{
		DWORD hookAddr = 0x4606B7;
		BYTE rawA[5];
		PVZ::Memory::ReadArray<BYTE>(hookAddr, rawA, 5);
		{
			static const BYTE kExpected[5] = { 0xE8, 0xF4, 0xE5, 0x00, 0x00 };
			if (memcmp(rawA, kExpected, 5) != 0)
			{
				CrashStr("HOOKSKIP name=Torchwood1 site=0x4606B7 (bytes changed - modifier?)\r\n");
				return;
			}
		}

		int tramp = (int)TRAMPOLINE_ALLOC();
		if (tramp == 0) return;

		BYTE tp[64];
		int p = 0;
		auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
		// rel32 必须用 DWORD(无符号) 运算：VirtualAlloc 可能返回高地址（int 视为负数）会溢出
		auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
		auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

		// [0]  cmp dword [esi+0x5C], 0    ; 确认 Pea（原生已保证，双保险）
		tp[p++] = 0x83; tp[p++] = 0x7E; tp[p++] = 0x5C; tp[p++] = 0x00;
		int jneOrig = p;
		tp[p++] = 0x75; tp[p++] = 0x00;    // jne ORIG (回填)
		tp[p++] = 0x60;                    // pushad
		tp[p++] = 0x56;                    // push esi (子弹)
		putRelCall((DWORD)&onPeaOnFire);   // cdecl，调用方清栈
		tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04; // add esp,4
		tp[p++] = 0x61;                    // popad
		// ORIG：原生 OnFire（Type→6 FirePea + 火球贴图/音效/粒子）
		*(BYTE*)(tp + jneOrig + 1) = (BYTE)(p - (jneOrig + 2)); // 回填 jne rel8
		putRelCall(0x46ECB0);
		putRelJmp(0x4606BC);              // 回到原流程（jmp 0x4606D0 前的跳转）

		PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
		int hookOff = tramp - ((int)hookAddr + 5);
		BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
		PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	}

	// ---- Hook B @ 0x4606CB（冰豌豆过火）----
	{
		DWORD hookAddr = 0x4606CB;
		BYTE rawB[5];
		PVZ::Memory::ReadArray<BYTE>(hookAddr, rawB, 5);
		{
			static const BYTE kExpected[5] = { 0xE8, 0x30, 0xE7, 0x00, 0x00 };
			if (memcmp(rawB, kExpected, 5) != 0)
			{
				CrashStr("HOOKSKIP name=Torchwood2 site=0x4606CB (bytes changed - modifier?)\r\n");
				return;
			}
		}

		int tramp = (int)TRAMPOLINE_ALLOC();
		if (tramp == 0) return;

		BYTE tp[64];
		int p = 0;
		auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
		auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
		auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

		// [0]  cmp byte [esi+0x5C], 1     ; 确认 SnowPea
		tp[p++] = 0x80; tp[p++] = 0x7E; tp[p++] = 0x5C; tp[p++] = 0x01;
		int jneOrig = p;
		tp[p++] = 0x75; tp[p++] = 0x00;    // jne ORIG (回填)
		tp[p++] = 0x60;                    // pushad
		tp[p++] = 0x56;                    // push esi (子弹)
		putRelCall((DWORD)&onSnowPeaFire); // 返回 eax: 0=走原生, 1=已处理
		tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04; // add esp,4
		// ★ popad 会恢复 EAX，返回值会被覆盖！先写入 pushad 的 EAX 槽位 [esp+0x1C]
		tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x1C; // mov [esp+0x1C], eax
		tp[p++] = 0x61;                    // popad
		tp[p++] = 0x85; tp[p++] = 0xC0;    // test eax, eax
		int jnzSkip = p;
		tp[p++] = 0x75; tp[p++] = 0x00;    // jnz SKIP (回填)
		// ORIG：原生 0x46EE00（冰豌豆→普通豌豆）
		// ★★ 2026-09-01 崩溃修复（崩溃日志 eip=0x46EE05 fault=0x78 edi=0）：原版调用约定
		//   eax=esi=子弹（0x4606C9 mov eax,esi），0x46EE03 mov edi,eax → 0x46EE05 读 [edi+0x78]。
		//   但上方 mov [esp+0x1C],eax + popad 把 eax 变成了 onSnowPeaFire 的返回值(0)，
		//   ORIG call 0x46EE00 时 eax=0 → edi=0 → 空指针崩溃。ORIG 分支必须恢复 eax=esi。
		*(BYTE*)(tp + jneOrig + 1) = (BYTE)(p - (jneOrig + 2)); // 回填 jne rel8
		tp[p++] = 0x8B; tp[p++] = 0xC6;    // mov eax, esi（恢复原版调用约定：eax=子弹）
		putRelCall(0x46EE00);
		// SKIP：已处理（冰火豆），跳过原生
		*(BYTE*)(tp + jnzSkip + 1) = (BYTE)(p - (jnzSkip + 2)); // 回填 jnz rel8
		putRelJmp(0x4606D0);              // 继续原流程（下一个子弹）

		PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
		int hookOff = tramp - ((int)hookAddr + 5);
		BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
		PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	}
}

// ==================== 剧毒体系：核心实现（海蘑菇首发）====================

// 读僵尸剧毒层数（0=无毒）
static int GetPoisonStacks(DWORD zombieAddr)
{
	auto it = g_poisonStacks.find(zombieAddr);
	return (it != g_poisonStacks.end()) ? it->second : 0;
}

// 附加剧毒（毒系植物共用入口）。
// sourcePlant：毒来源植物地址（0=不记录）；非 0 时写 zombie+0x148，
//   使"毒死的僵尸经验归毒来源植物"（含毒爆溅射附毒场景，溅射不经过子弹命中路径）。
// ★ 本函数在事件回调帧内调用（onProjectileHitZombie），std::map 操作与
//   g_projectileShooterMap 同量级，项目内已有多处先例，安全。
static void AddPoisonStacks(DWORD zombieAddr, int layers, DWORD sourcePlant)
{
	if (layers <= 0) return;
	auto it = g_poisonStacks.find(zombieAddr);
	if (it != g_poisonStacks.end())
		it->second += layers;
	else
		g_poisonStacks[zombieAddr] = layers;
	if (sourcePlant)
		MemSafeWrite<int>(zombieAddr + 0x148, (int)sourcePlant);
}

// ==================== 海蘑菇毒爆粒子特效 ====================
// 复刻 S6 幽冥菇"大星星子弹命中爆散"结构：中心闪光 + 一堆小光点外飞/旋转/渐隐，
// 星星换成海蘑菇孢子（整体乘绿色色调）。全部走原版粒子系统，零新增资源文件。
//
// 已验证的调用约定（原版函数表.xlsx + 反汇编 + S6 CT 原文三方交叉确认）：
//   LawnApp::AddTodParticle @ 0x453C80
//     eax = ParticleEffect 枚举（0x1D=STAR 即 StarSplat：杨桃星星命中特效）
//     ecx = renderOrder（原版游戏内 4 处特效调用 + S6 全部用 0x61A80）
//     edx = LawnApp（[0x6A9EC0]）
//     栈参：[esp]=X、[esp+4]=Y（Y 先 push、X 后 push，后 push 在栈顶）
//     stdcall ret 8，自清两个浮点栈参；eax 返回 TodParticleSystem*
//   TodParticleSystem::OverrideColor @ 0x518560
//     ebx = 发射器名指针（0 = 全部发射器），esi = 粒子系统
//     栈参：[esp] = TodColor*（指向 R,G,B,A 四字节，乘色）
//     裸 ret（cdecl），调用方自己清栈（颜色 4 字节 + 指针 1 字节 = 20）
//   乘色说明：Star_splats / Star_particles 是黄白色系，乘绿后 ≈ 纯绿光点。
// ★ float 一律以原始位模式 push（跨 __asm 传 float 局部不可靠——ST0 被冲，铁律）
// ★ __asm 读写一律走文件级全局变量（hook 帧内 __asm 引用局部变量有 MSVC 偏移错位前科）
static DWORD g_burstPsysOut = 0;   // AddTodParticle 返回值中转
static DWORD g_burstXBits = 0;     // X 的 float 位模式
static DWORD g_burstYBits = 0;     // Y 的 float 位模式
static int   g_burstFxId = 0;      // ParticleEffect 枚举
static DWORD g_burstLawn = 0;      // LawnApp 指针中转
static DWORD g_burstPsysAddr = 0;  // OverrideColor / OverrideImage 的 this
static int   g_burstOvrR = 0, g_burstOvrG = 0, g_burstOvrB = 0;
static DWORD g_burstImgSel = 0;    // OverrideImage 的贴图指针中转
static int g_seaBurstFxErr = 0;    // __except 留痕计数（排障铁律：空实现是盲区）

// 孢子贴图指针缓存：从粒子定义表纯读获取（游戏启动时已随 main.pak 全量加载，零新增资源）
//   定义表 = [0x6A9F0C] 是 TodParticleDefinition 结构体数组（8 字节/项，0x518A82 原版铁证）：
//     [defArr + effectId*8 + 0] = TodEmitterDefinition* mEmitterDefs
//     [defArr + effectId*8 + 4] = int mEmitterDefCount
//   TodEmitterDefinition 首字段 = Image* mImage（+0x00）
//   贴图来源定义：FumeCloud → PuffShroom_puff1（大喷菇雾团）、PuffSplat → PuffShroom_puff2（小喷菇孢子）
static DWORD g_burstImgPtr[3] = { 0, 0, 0 }; // [1]=puff1 [2]=puff2，下标即 INI 的 IMAGE 编号
static int   g_seaBurstImgErr = 0;           // 解析失败留痕（失败自动重试；成功后自停）

// 手写子串匹配（hook 内禁 CRT，纯指令逐字节）——定义表文件名是全路径
// "particles\PuffSplat.xml"，必须用子串包含而非全等比较（全等永远失配 = 贴图替换失效根因）
static int SeaBurstStrContains(DWORD hay, const char* needle)
{
	if (!hay || !needle || !needle[0])
		return 0;
	for (int start = 0; start < 48; start++)
	{
		int k = 0;
		while (needle[k] != 0)
		{
			char c1 = MemSafeRead<char>(hay + start + k);
			if (c1 != needle[k])
				break;
			k++;
		}
		if (needle[k] == 0)
			return 1;
		if (MemSafeRead<char>(hay + start) == 0)
			return 0; // 主串已尽
	}
	return 0;
}

// 按定义文件名子串在 ParticleParams 表里查 effectId，再从定义表取首发射器贴图指针。
// ★ 只读定义表取 Image*，绝不写定义表/游戏资源——贴图覆盖是 per-instance（实例 +0x54 槽）。
// ★ 定义表布局（0x518A82 原版代码 lea ebx,[eax+ebp*8] 铁证）：[0x6A9F0C] 是
//   TodParticleDefinition 结构体数组（8 字节/项）：+0=mEmitterDefs*、+4=mEmitterDefCount。
//   不是"指针数组"！旧版 [id*8+4] 取到的是数量小整数当指针 → 解引用崩溃（__except 吞掉
//   后连染色都中断 = "彻底变原版"根因）。
static DWORD SeaBurstFindDefImage(const char* defName)
{
	int paramCount = MemSafeRead<int>(0x6A9F10);    // gParticleParamArraySize
	DWORD paramArr = MemSafeRead<DWORD>(0x6A9F14);  // gParticleParamArray {int effect; const char* name}
	DWORD defArr = MemSafeRead<DWORD>(0x6A9F0C);    // gParticleDefArray（结构体数组基址）
	if (!paramArr || !defArr || paramCount <= 0 || paramCount > 4096)
		return 0;
	for (int i = 0; i < paramCount; i++)
	{
		DWORD namePtr = MemSafeRead<DWORD>(paramArr + i * 8 + 4);
		if (!SeaBurstStrContains(namePtr, defName))
			continue;
		int effectId = MemSafeRead<int>(paramArr + i * 8);
		if (effectId < 0 || effectId > 512)
			return 0;
		DWORD emitterDefs = MemSafeRead<DWORD>(defArr + effectId * 8 + 0); // [项+0]=mEmitterDefs*
		int emitterCount = MemSafeRead<int>(defArr + effectId * 8 + 4);    // [项+4]=数量
		if (!emitterDefs || emitterCount < 1)
			return 0;
		return MemSafeRead<DWORD>(emitterDefs); // mEmitterDefs[0].mImage（+0x00）
	}
	return 0;
}

// 解析孢子贴图（毒爆时调用；缺失项自动重试，成功后缓存不再进入）
static void SeaBurstResolveImages()
{
	int missing = 0;
	if ((g_seaBurstImage1 == 1 || g_seaBurstImage2 == 1) && !g_burstImgPtr[1])
	{
		g_burstImgPtr[1] = SeaBurstFindDefImage("FumeCloud");
		if (!g_burstImgPtr[1])
			missing = 1;
	}
	if ((g_seaBurstImage1 == 2 || g_seaBurstImage2 == 2) && !g_burstImgPtr[2])
	{
		g_burstImgPtr[2] = SeaBurstFindDefImage("PuffSplat");
		if (!g_burstImgPtr[2])
			missing = 1;
	}
	if (missing)
		g_seaBurstImgErr++;
}

// 生成一个粒子特效，返回 TodParticleSystem*（失败/非法配置返回 0）
static DWORD g_burstRenderOrder = 0x61A80;   // asm 读取（可自定义渲染序，见 Ex 版）

static DWORD SeaBurstSpawnParticleEx(float x, float y, int effectId, DWORD renderOrder)
{
	if (effectId < 0)
		return 0;
	g_burstLawn = MemSafeRead<DWORD>(0x6A9EC0);
	if (!g_burstLawn)
		return 0;
	g_burstXBits = *(DWORD *)&x;   // float → 位模式
	g_burstYBits = *(DWORD *)&y;
	g_burstFxId = effectId;
	g_burstRenderOrder = renderOrder;
	__asm
	{
		pushad
		mov eax, g_burstFxId
		mov ecx, g_burstRenderOrder ; renderOrder（默认 0x61A80 原版特效通用值）
		push g_burstYBits         ; Y → [esp+4]
		push g_burstXBits         ; X → [esp]（后 push 在栈顶）
		mov edx, g_burstLawn
		mov ebx, 0x453C80
		call ebx                  ; stdcall ret 8，自清 X/Y
		mov g_burstPsysOut, eax
		popad
	}
	return g_burstPsysOut;
}

static DWORD SeaBurstSpawnParticle(float x, float y, int effectId)
{
	return SeaBurstSpawnParticleEx(x, y, effectId, 0x61A80);
}

// 粒子系统整体改色（乘色，发射器名 NULL = 全部发射器）
// ★ 调用约定以 pvzclass 官方 TodParticleSystem::OverrideColor 封装为准（实测可用）：
//   ebx = 发射器名指针（0=全部）——必须保持到 call 时刻，函数地址只能用 eax 中转！
//   栈参（call 前）：[esp]=this（粒子系统）、[esp+4]=TodColor*（指向栈上 R,G,B,A）、
//   [esp+8..]=R,G,B,A（push 序：A,B,G,R）；函数 stdcall ret 8 弹掉 this+TodColor*，
//   调用方 add esp,16 清 4 个颜色 dword。
//   （旧版按"esi=this + 裸 ret + add 20"调用，且 mov ebx,0x518560 把发射器名指针
//     覆盖成了函数地址 → 改色静默失败 = 毒爆只见杨桃动画没有绿色的根因，已废。）
static void SeaBurstOverrideColor(DWORD psysAddr, int r, int g, int b)
{
	if (!psysAddr)
		return;
	g_burstPsysAddr = psysAddr;
	g_burstOvrR = r;
	g_burstOvrG = g;
	g_burstOvrB = b;
	__asm
	{
		pushad
		xor ebx, ebx              ; 发射器名 = NULL → 全部发射器（保持到 call）
		push 0xFF                 ; A（栈上构造 TodColor{R,G,B,A}）
		push g_burstOvrB
		push g_burstOvrG
		push g_burstOvrR          ; R 在栈顶方向
		push esp                  ; TodColor* → [esp+4]（this 压栈后）
		push g_burstPsysAddr      ; this → [esp]（栈参，非 esi！）
		mov eax, 0x518560
		call eax                  ; stdcall ret 8（弹 this + TodColor*）
		add esp, 16               ; 清 R/G/B/A 4 个 dword
		popad
	}
}

// 粒子系统整体替换贴图（per-instance 覆盖发射器实例 +0x54 槽，不影响其它同特效实例）
// 调用约定（0x518600 反汇编实证）：edx = TodParticleSystem* this，esi = Image*，裸 ret 无栈参。
// 注意：一次调用把该粒子系统所有发射器的贴图统一覆盖为同一张图。
static void SeaBurstOverrideImage(DWORD psysAddr, DWORD imgPtr)
{
	if (!psysAddr || !imgPtr)
		return;
	g_burstPsysAddr = psysAddr;
	g_burstImgSel = imgPtr;
	__asm
	{
		pushad
		mov esi, g_burstImgSel
		mov edx, g_burstPsysAddr
		mov ebx, 0x518600
		call ebx                  ; 裸 ret，无栈参
		popad
	}
}

// 毒爆外观入口：在 (hitX, hitY) 处爆一团绿色孢子。
// __try 留痕：粒子调用本身与游戏原生特效同路径（低危），但毒爆在 hook 帧内，
// 任何异常只跳过特效绝不能带崩游戏。fxErr++ 留痕便于排查。
static void SeaShroomBurstFX(float hitX, float hitY)
{
	__try
	{
		if (!g_seaBurstParticleEnabled)
			return;
		// 先 spawn（顺带确保 0x46 及孢子定义已加载），再解析贴图，最后染色+换贴图
		DWORD psys = SeaBurstSpawnParticle(hitX, hitY, g_seaBurstEffect1);
		SeaBurstResolveImages();
		SeaBurstOverrideColor(psys, g_seaBurstTintR, g_seaBurstTintG, g_seaBurstTintB);
		if (g_seaBurstImage1 > 0 && g_seaBurstImage1 < 3 && g_burstImgPtr[g_seaBurstImage1])
			SeaBurstOverrideImage(psys, g_burstImgPtr[g_seaBurstImage1]);
		// 叠加特效：同为 0x46（看星星）再放一层，不同贴图制造"孢子+雾团"混喷
		if (g_seaBurstEffect2 >= 0)
		{
			DWORD psys2 = SeaBurstSpawnParticle(hitX, hitY, g_seaBurstEffect2);
			SeaBurstOverrideColor(psys2, g_seaBurstTintR, g_seaBurstTintG, g_seaBurstTintB);
			if (g_seaBurstImage2 > 0 && g_seaBurstImage2 < 3 && g_burstImgPtr[g_seaBurstImage2])
				SeaBurstOverrideImage(psys2, g_burstImgPtr[g_seaBurstImage2]);
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_seaBurstFxErr++;
	}
}

// 毒爆 3×3 溅射附毒（独立函数：内部含 std::vector 需要析构，
// 与 __try 同函数会触发 C2712"无法在要求对象展开的函数中使用 __try"）
static void SeaShroomSplash(DWORD zombieAddr, int row, float hitX, DWORD sourcePlant, DWORD boardAddr)
{
	if (!boardAddr) return;
	PVZ::Board board(boardAddr);
	auto allZombies = board.GetAllZombies();
	for (auto& z : allZombies)
	{
		if (z.GetBaseAddress() == zombieAddr) continue; // 目标下面清零，不再重复附毒
		if (z.NotExist) continue;
		// ★ 目标筛选（用户规格 2026-09-24：能打潜水，不能打气球和矿工）：
		//   DRF_GROUND|DRF_SUBMERGED = 地面 + 潜水可附毒；
		//   气球(FLYING/FALLING)、未出土矿工(DIGGER_DIG/DRILL/LOST_DIG/LANDING)、
		//   墓碑出土中(RISING_FROM_GROUND)全部排除——与火豌豆溅射同用 EffectedBy 判定。
		if (!z.EffectedBy(PVZ::DRF_GROUND | PVZ::DRF_SUBMERGED)) continue;
		int zrow = MemSafeRead<int>(z.GetBaseAddress() + 0x1C);
		if (abs(zrow - row) > 1) continue;
		float dx = z.X - hitX;
		if (dx < -POISON_BURST_RADIUS_PX || dx > POISON_BURST_RADIUS_PX) continue;
		AddPoisonStacks(z.GetBaseAddress(), POISON_BURST_SPLASH_STACKS, sourcePlant);
	}
}

// 海蘑菇 5阶毒爆：对目标造成 15×层数 直伤（走 Hit 正常流程=优先防具），
// 并给 3×3 范围内所有僵尸附加 10 层毒（含目标，其层数已≥阈值）。
// ★ 毒爆后目标剧毒层数清零（用户规格：爆完重新叠毒）+ SetColor 白恢复原色。
// boardAddr 用于 GetAllZombies 遍历；sourcePlant=海蘑菇（溅射附毒写来源）。
static void SeaShroomBurst(DWORD zombieAddr, DWORD sourcePlant, DWORD boardAddr)
{
	int stacks = GetPoisonStacks(zombieAddr);
	if (stacks <= 0) return;

	// 目标信息先读（Hit 可能致死，X/行号仍可读）
	int row = MemSafeRead<int>(zombieAddr + 0x1C);
	float hitX = MemSafeRead<float>(zombieAddr + 0x2C);
	float hitY = MemSafeRead<float>(zombieAddr + 0x30); // 僵尸 Y（行基线）

	// ★ 毒爆粒子：绿色孢子爆散（复刻 S6 幽冥菇星星命中爆散，STAR 特效乘绿；
	//   放在 Hit 之前调用避免目标死亡后坐标仍可读带来的歧义，位置 = 命中僵尸身体中心）
	// 爆点 = 命中僵尸身体中心 + INI 可调偏移（OFFSET_X 右正 / OFFSET_Y 下正）
	SeaShroomBurstFX(hitX + (float)g_seaBurstOffsetX, hitY - 40.0f + (float)g_seaBurstOffsetY);

	// 15倍层数直伤
	PVZ::Zombie target(zombieAddr);
	if (!target.NotExist)
		target.Hit(stacks * POISON_BURST_DMG_MULT, PVZ::DAMAGEF_NONE);

	// 3×3 溅射附毒（独立函数，含 vector）
	SeaShroomSplash(zombieAddr, row, hitX, sourcePlant, boardAddr);

	// 毒爆后目标层数清零 + 恢复原色（仅目标仍存活时有效；已死则 reanim 随移除销毁）
	__try
	{
		PVZ::Animation anim2(0);
		if (TryGetZombieReanim(zombieAddr, anim2))
		{
			PVZ::Color white = { 0xFF, 0xFF, 0xFF, 0xFF };
			anim2.SetColor(white);
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
	g_poisonStacks.erase(zombieAddr);
}

// 剧毒每帧轮询 Inner（无 __try——内部含 std::vector 需析构，与 __try 同函数触发 C2712；
// __try 外壳在 UpdatePoisonFrame，金盏花 UpdateMarigoldFrame/Inner 同模式）：
//   ①每帧 UnLock(AP_ZOMBIECOLOR)：游戏原生 0x52D3EA 栈取色会忽略 reanim 颜色
//     （v1 SetColor 无效根因）；UnLock 写 0x909030EB jmp 启用 reanim 颜色，每帧重写防 0x52xxxx 重置。
//   ②每帧遍历**所有僵尸**按状态设置 reanim 基础色（UnLock 后游戏栈色路径被跳过，
//     原版减速蓝/冻结/黄油/魅惑色全部消失 → 由我们模拟恢复）：
//     带毒→绿（毒优先） > 魅惑→紫 > 减速→浅蓝 > 其他→白
//     ★ 颜色值均为乘法 tint 近似（原版精确值不可得，测试后可按反馈微调）
//   ③每 1 秒 tick：层数>0 僵尸造成"层数"点伤害（Hit 正常流程=优先防具）。
//   ④兜底清理：僵尸已移除（NotExist）→ erase（正常移除路径由 onZombieRemove 清理）。
// ---- 闪白诊断（一次性捕获，纯 Win32 落盘，禁 CRT 铁律）----
// ★ 状态：已完成使命——原版闪白公式已从二轮数据定案（见染色 tick 处注释：
//   Additive.RGB = cnt*10），g_flashDiagEnabled 默认 0 关闭自动诊断，
//   染色从第 1 帧就正常工作。需要重新取证时改回 1 再跑一次 build。
// 目的：原版受击闪白是平滑淡入淡出，但实现代码在 0x52xxxx 运行时解密区，
//   文件反汇编不可信。诊断期重新上锁（SafeLockZombieColor 恢复原版着色代码）、
//   暂停我们自己的染色 SetColor，让游戏原版自由写 reanim 颜色通道——
//   逐帧 dump 首只受击僵尸的 reanim[0x40..0xB0]（覆盖乘色0x48/加算0x6C/覆盖0x80
//   三通道 + 各开关字节），外加 runtime dump 0x52D300..0x52D4C0 原版着色代码
//   （解密后真实字节，可离线反汇编还原精确公式）。
// 捕获完成自动恢复正常染色；超时 3600 帧自动放弃（诊断期毒绿/减速蓝会短暂消失）。
static int   g_flashDiagEnabled = 0;  // ★0=关闭（公式已定案）；1=重新启用自动诊断
static int   g_flashDiagDone = 0;     // 1=捕获完成/中止（恢复正常染色）
static int   g_flashDiagFrames = 0;   // 诊断模式经过的轮询帧数（超时保护）
static DWORD g_flashDiagReanim = 0;   // 捕获目标的 reanim 地址（0=未锁定）
static int   g_flashDiagPre = 0;      // 0=还没写静息基线
static int   g_flashDiagAfter = 0;    // cnt 归零后的收尾采样计数
static int   g_flashDiagLines = 0;    // 已写样本行数（上限保护）
static int   g_flashDiagProbes = 0;   // PRB 探针行计数（上限保护）
static int   g_flashDiagCodeDone = 0; // CODE dump 是否已写（只写一次）
static int   g_flashDiagLost = 0;     // 目标僵尸连续未找到帧数（死亡换弹保护）
static const char FLASHDIAG_HEX[] = "0123456789ABCDEF";

static void FlashDiagAppend(const char* buf, int len)
{
	HANDLE h = CreateFileA("D:\\pvz_flash_diag.txt", GENERIC_WRITE, FILE_SHARE_READ,
		NULL, OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
	if (h != INVALID_HANDLE_VALUE)
	{
		SetFilePointer(h, 0, NULL, FILE_END);
		DWORD w = 0;
		WriteFile(h, buf, (DWORD)len, &w, NULL);
		CloseHandle(h);
	}
}

// 一行样本：tag + 闪白计数 + reanim[0x40..0xB0] 十六进制（112 字节 = 乘色/加算/覆盖/开关全覆盖）
static void FlashDiagWriteSample(const char* tag, DWORD ra, int cnt)
{
	char buf[640];
	int p = 0;
	const char* s = tag;
	while (*s && p < 16) buf[p++] = *s++;
	buf[p++] = ' ';
	{
		char t[16];
		int v = cnt, n = 0;
		if (v == 0) t[n++] = '0';
		while (v > 0 && n < 15) { t[n++] = (char)('0' + v % 10); v /= 10; }
		while (n > 0) buf[p++] = t[--n];
	}
	buf[p++] = ' ';
	for (int i = 0; i < 0x70; i++)
	{
		BYTE b = MemSafeRead<BYTE>(ra + 0x40 + i);
		buf[p++] = FLASHDIAG_HEX[(b >> 4) & 0xF];
		buf[p++] = FLASHDIAG_HEX[b & 0xF];
		if ((i & 15) == 15) buf[p++] = ' ';
	}
	buf[p++] = '\r'; buf[p++] = '\n';
	FlashDiagAppend(buf, p);
}

// 原版着色/闪白代码区（0x52D3EA 解锁补丁所在函数段）运行时真实字节，供离线反汇编
static void FlashDiagWriteCode()
{
	const DWORD START = 0x52D300;
	const DWORD END   = 0x52D4C0;
	char buf[128];
	for (DWORD a = START; a < END; a += 16)
	{
		int p = 0;
		const char* s = "CODE ";
		while (*s) buf[p++] = *s++;
		for (int sh = 28; sh >= 0; sh -= 4) buf[p++] = FLASHDIAG_HEX[(a >> sh) & 0xF];
		buf[p++] = ' ';
		for (int i = 0; i < 16 && a + i < END; i++)
		{
			BYTE b = MemSafeRead<BYTE>(a + i);
			buf[p++] = FLASHDIAG_HEX[(b >> 4) & 0xF];
			buf[p++] = FLASHDIAG_HEX[b & 0xF];
		}
		buf[p++] = '\r'; buf[p++] = '\n';
		FlashDiagAppend(buf, p);
	}
}

// 闪白诊断帧。返回 1 = 诊断仍活跃（调用方跳过染色，保持游戏原版着色）。
static int FlashDiagFrame()
{
	if (!g_flashDiagEnabled)
		return 0;
	if (g_flashDiagDone)
		return 0;
	g_flashDiagFrames++;
	if (g_flashDiagFrames > 3600)
	{
		g_flashDiagDone = 1;   // 超时放弃：恢复染色（正常流程下帧重新 UnLock）
		if (!g_flashDiagCodeDone)
		{
			g_flashDiagCodeDone = 1;
			FlashDiagWriteCode();
		}
		FlashDiagAppend("DIAGEND\r\n", 9);
		return 1;
	}
	SafeLockZombieColor();     // 诊断期让原版着色代码运行（幂等）
	DWORD la = MemSafeRead<DWORD>(0x6A9EC0);
	if (!la) return 1;
	int board = MemSafeRead<int>(la + 0x768);
	if (!board) return 1;
	PVZ::Board b(board);
	auto zombies = b.GetAllZombies();
	int found = 0;
	for (auto& z : zombies)
	{
		if (z.NotExist) continue;
		DWORD za = z.GetBaseAddress();
		int cnt = MemSafeRead<int>(za + 0x54);
		PVZ::Animation anim(0);
		if (!TryGetZombieReanim(za, anim))
			continue;
		DWORD ra = anim.GetBaseAddress();
		if (!g_flashDiagReanim)
		{
			// 静息基线：任意未受击僵尸的 reanim（各通道静息值/开关字节）
			if (cnt <= 0 && !g_flashDiagPre)
			{
				g_flashDiagPre = 1;
				FlashDiagWriteSample("PRE", ra, 0);
				// v2：CODE dump 不依赖捕获，PRE 后立即写（进关卡即得，
				// 无需等玩家命中僵尸；首轮即因"等捕获完成"而丢失过 CODE）
				if (!g_flashDiagCodeDone)
				{
					g_flashDiagCodeDone = 1;
					FlashDiagWriteCode();
				}
			}
			// 锁定新鲜受击（v2：阈值降为 ≥1——计数器量程未知，首轮 ≥20 从未触发；
			// cnt 值本身记录在每行样本里，曲线完整与否由样本自证）
			if (cnt >= 1)
			{
				g_flashDiagReanim = ra;
				FlashDiagWriteSample("LOCK", ra, cnt);
				g_flashDiagLines = 1;
				g_flashDiagLost = 0;
			}
			else if (g_flashDiagProbes == 0)
			{
				// PRB 探针（仅一次）：未锁定时 dump 僵尸本体 +0x40..0xB0（含 +0x54
				// 计数器邻域字段布局，注意这里 dump 的是僵尸结构不是 reanim）
				g_flashDiagProbes = 1;
				FlashDiagWriteSample("PRB", za, cnt);
			}
		}
		else if (ra == g_flashDiagReanim)
		{
			found = 1;
			FlashDiagWriteSample("SMP", ra, cnt);
			g_flashDiagLines++;
			if (cnt <= 0) g_flashDiagAfter++;
			else          g_flashDiagAfter = 0;
			if (g_flashDiagAfter >= 4 || g_flashDiagLines > 60)
			{
				g_flashDiagDone = 1;
				g_flashDiagReanim = 0;
				if (!g_flashDiagCodeDone)
				{
					g_flashDiagCodeDone = 1;
					FlashDiagWriteCode();   // 收尾兜底：PRE 阶段已写过则跳过
				}
				FlashDiagAppend("DIAGEND\r\n", 9);
			}
		}
	}
	if (g_flashDiagReanim && !found)
	{
		// 目标僵尸死亡/换弹（reanim 消失）：换下一只闪白继续捕
		if (++g_flashDiagLost > 10)
		{
			g_flashDiagReanim = 0;
			g_flashDiagLost = 0;
		}
	}
	return 1;
}

// ★ 毒伤走 Hit() 不写 zombie+0x148（TakeDamage 不维护来源字段），
//   毒死的僵尸经验仍归上次被海蘑菇子弹命中/附毒时写入的来源植物。
static void UpdatePoisonFrameInner(DWORD boardAddress)
{
	// ---- 闪白诊断期：暂停染色（解锁+SetColor），让游戏原版着色代码自由运行 ----
	// 捕获完成/超时后自动恢复。毒伤每秒 tick 不受影响（在函数后半段）。
	if (FlashDiagFrame())
		return;

	// ★每帧解锁僵尸颜色（详见 SafeUnlockZombieColor 注释：带字节校验防写坏代码）
	if (g_poisonTintEnabled)
		SafeUnlockZombieColor();

	// --- 全局状态色轮询（每帧，恢复原版减速/冻结/魅惑色 + 毒绿）---
	int board = MemSafeRead<int>(PVZ_BASE + 0x768);
	if (g_poisonTintEnabled && board)
	{
		PVZ::Board b(board);
		auto zombies = b.GetAllZombies();
		for (auto& z : zombies)
		{
			if (z.NotExist)
				continue;
			DWORD za = z.GetBaseAddress();
			PVZ::Color c = { 0xFF, 0xFF, 0xFF, 0xFF }; // 默认白（恢复）
			// 状态色优先级：毒绿 > 魅惑紫 > 减速蓝 > 白（恢复）
			if (GetPoisonStacks(za) >= 15)
				c = PVZ::Color{ 0x50, 0xFF, 0x50, 0xFF };   // 高于20层毒绿优先
			else if (z.Hypnotized)
				c = PVZ::Color{ 0xE8, 0x15, 0xFF, 0xFF };   // 魅惑紫（S6 CT 魅惑色 R232 G21 B255）
			else if (z.DecelerateCountdown > 0)
				c = PVZ::Color{ 0x15, 0x22, 0x80, 0xFF };   // 减速浅蓝（近似原版）
			else if (GetPoisonStacks(za) > 0)
				c = PVZ::Color{ 0x50, 0xFF, 0x50, 0xFF };   // 毒绿
			// ★ 受击闪白终版 = 原版精确公式（0x52D387 runtime 反汇编 + 逐帧 SMP 双铁证）：
			//   Additive(加算+0x6C).RGB = JustGotShotCounter(z+0x54) * 10，Alpha=255；
			//   cnt<=0 → (0,0,0,255)（静息=零加算）；乘色/覆盖通道不碰（状态色不受闪白影响）。
			//   计数 25→0 每 10ms 逻辑 tick 递减 1（30fps 渲染下 ~8 帧，与用户录像实测吻合）。
			//   原版汇编：lea ecx,[ecx+ecx*4]; add ecx,ecx（×10）; push 0xFF; push ecx。
			PVZ::Animation anim(0);
			if (TryGetZombieReanim(za, anim))
			{
				int fc = MemSafeRead<int>(za + 0x54);
				if (fc > 0)
				{
					if (fc > 25) fc = 25;   // 理论上限 25（原版 TakeDamage 设 25），防异常大值
					int k = fc * 10;        // 0..250，与原版一致
					anim.SetAdditiveColor(PVZ::Color{ k, k, k, 0xFF });
				}
				else
				{
					anim.SetAdditiveColor(PVZ::Color{ 0, 0, 0, 0xFF }); // 静息：零加算
				}
				anim.SetColor(c);
			}
		}
	}

	if (g_poisonStacks.empty())
		return;

	// --- 每秒 tick 伤害 ---
	int now = MemSafeRead<int>(boardAddress + 0x5568); // Board.PlayingTime
	if (now - g_poisonLastTickCs < POISON_TICK_INTERVAL_CS)
		return;
	g_poisonLastTickCs = now;

	for (auto it = g_poisonStacks.begin(); it != g_poisonStacks.end(); )
	{
		DWORD za = it->first;
		if (MemSafeRead<BYTE>(za + 0xEC)) // NotExist → 兜底清理
		{
			it = g_poisonStacks.erase(it);
			continue;
		}
		if (it->second > 0)
		{
			PVZ::Zombie z(za);
			if (!z.NotExist)
				z.Hit(it->second, PVZ::DAMAGEF_NONE); // 每秒"层数"点伤害，优先防具
		}
		++it;
	}
}

// 剧毒每帧轮询入口（__try 外壳：Inner 含 vector 无法自带 __try（C2712），
// 外壳无本地对象、只包调用——金盏花 UpdateMarigoldFrame/Inner 同模式）
static void UpdatePoisonFrame(DWORD boardAddress)
{
	__try
	{
		UpdatePoisonFrameInner(boardAddress);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ==================== 豌豆子弹染色：reanim 轨道染色（Type 6 火球）====================
// ★ 根因（2026-08-28 两次无效后最终确认）：火球豌豆（Type 6）的视觉 = Reanim 动画，
//   不是 46E805 的 DrawImage 路径！Projectile::Draw（0x46E540）里 Type 6 分支
//   （0x46E5C5 mov [esp+0xC],0）→ 46E6D9 test ecx,ecx; je 0x46E828 直接跳过主贴图绘制。
//   火球动画 = [proj+0x7C] 指向的子 Reanimator（[6A9EB8]+0xC 池，0x30C/项），
//   绘制时递归遍历（0x404D10 类型3），内部轨道若为类型2 → 0xA0 池项
//   （=PVZ::Animation 布局：+0x14 NotExist / +0x48..0x54 颜色，剧毒机制已验证）。
// 方案（同剧毒机制）：每帧轮询，解析 [proj+0x7C] → 0x30C 子 Reanimator → 类型2 轨道
//   → 0xA0 池项 → 写 +0x48..0x54 颜色；SafeUnlockZombieColor 解锁 0x52D3EA 全局取色。
// 依赖反汇编：46E865-46E87C（0x30C 池查表）、0x404D10 类型2（0xA0 池查表）。

// 解析 [proj+0x7C] → 0x30C 子 Reanimator → 找类型2 轨道 → 返回 0xA0 池项地址（0=失败）
static DWORD GetProjectileFireTrackAnim(DWORD projAddr)
{
	if (!projAddr) return 0;
	// 1) [proj+0x7C] = 子 Reanimator ID（低16位=索引），查 [6A9EB8]+0xC 池（0x30C/项）
	int id3 = MemSafeRead<int>(projAddr + 0x7C);
	int idx3 = id3 & 0xFFFF;
	if (idx3 <= 0 || idx3 > 4096) return 0;
	int base = MemSafeRead<int>(0x6A9EB8);
	if (base < 0x10000) return 0;
	int tbl3 = MemSafeRead<int>(base + 0xC);
	if (tbl3 < 0x10000) return 0;
	int cnt3 = MemSafeRead<int>(tbl3 + 8);
	if (idx3 >= cnt3) return 0;
	int item3 = MemSafeRead<int>(tbl3) + idx3 * 0x30C;
	if (item3 < 0x100000) return 0;
	if (MemSafeRead<int>(item3 + 0x308) != id3) return 0;   // ID 校验
	int trackCount = MemSafeRead<int>(item3 + 0x300);
	if (trackCount <= 0 || trackCount > 16) return 0;
	// 2) 遍历轨道记录（0x30/条，从 item3+0 起）：类型2（0xA0 池）→ 池项 = [[base+8]] + idx*0xA0
	for (int i = 0; i < trackCount; i++)
	{
		int rec = item3 + i * 0x30;
		int rtype = MemSafeRead<int>(rec + 4);
		if (rtype != 2) continue;
		int rid = MemSafeRead<int>(rec);
		int idx = rid & 0xFFFF;
		if (idx <= 0 || idx > 8192) continue;
		int tbl2 = MemSafeRead<int>(base + 8);
		if (tbl2 < 0x10000) continue;
		int cnt2 = MemSafeRead<int>(tbl2 + 8);
		if (idx >= cnt2) continue;
		int anim = MemSafeRead<int>(tbl2) + idx * 0xA0;
		if (anim < 0x100000) continue;
		if (MemSafeRead<BYTE>(anim + 0x14)) continue;   // NotExist → 跳过
		if (!CrashIsWritable(anim, 0xA0)) continue;                 // 整块可写安全网
		return anim;
	}
	return 0;
}

// Reanim 轨道贴图覆盖（0x473490：ecx=reanim实例, eax=轨道名, [esp]=image, ret 4）
// ★ 直接内联汇编调用——本质是纯内存写 轨道[idx]+0x44（FindTrackIndex 按名查索引），
//   不走 Memory::Execute（每帧轮询禁远程线程，金盏花 SetImageOverride 封装即此函数）。
static void ReanimSetImageOverride(DWORD reanimAddr, const char* trackName, DWORD imageAddr)
{
	if (!reanimAddr || !imageAddr || !trackName) return;
	// ★★★ 2026-10-16 任意地址写闸门（按反汇编实证重写，不是猜）：
	//   0x473490 的实际代码是：
	//        call 0x472F30(reanim,name)   ; FindTrackIndex：遍历 [reanim+0xC] 名字表 strcmp
	//        mov edx,[ebx+0x58]           ; 轨道实例数组
	//        lea ecx,[eax+eax*2]; shl ecx,5
	//        mov [ecx+edx+0x44], eax      ; 实例数组 + idx*0x60 + 0x44
	//   两个要点（都已现场核对字节）：
	//     ① 0x472F30 **找不到时返回 0（不是 -1）** ⇒ 历史上所有
	//        `if (FindTrackIndex(name) < 0) return;` 的"防护"从来没生效过；
	//        真正的致命情形是 ②。
	//     ② reanim 指针本身是垃圾时（典型：动画未就绪，框架返回 INVALID_BASEADDRESS
	//        = 0x400000 = exe 镜像基址，`if (!GetBaseAddress())` 拦不住），
	//        [reanim+0xC] 会把 PE 头当"名字表"，count/实例数组指针全是垃圾
	//        ⇒ 算出任意 idx、任意基址 → `mov [ecx+edx+0x44], eax` **任意地址写**
	//        ⇒ 写坏 CRT 堆 → 之后任意一次堆操作在 ntdll 里 fault=0 随机崩。
	//   所以这里按顺序卡死：reanim 必须是"可写的堆对象"→ 轨道名必须真能精确命中
	//   （索引落在 [0,count) 内）→ 目标 0x60 字节必须整块可写。三者任一不过就拒绝调用。
	if (reanimAddr == 0x400000 || reanimAddr >= 0x80000000) return;
	if (!CrashIsWritable(reanimAddr, 0xA0)) return;      // reanim 对象本身必须是可写堆内存
	int idx = ReanimTrackIndex(reanimAddr, trackName);   // 精确匹配，未命中返回 -1
	if (idx < 0) return;
	int inst = MemSafeRead<int>(reanimAddr + 0x58);
	if (inst < 0x10000) return;
	if (!CrashIsWritable((DWORD)inst + (DWORD)idx * 0x60, 0x60)) return;
	static DWORD s_reanim = 0;
	static DWORD s_image = 0;
	static const char* s_name = nullptr;
	s_reanim = reanimAddr;
	s_name = trackName;
	s_image = imageAddr;
	__asm {
		// ★★ pushad/popad 必须：0x473490 只自保 ebx，eax/ecx/edx 会被它改掉；
		//    而调用方是 onGameObjectsUpdate 巨型函数，FPO 帧指针就放在 ebx 上——
		//    少了这对指令会毁掉栈帧，表现为后续访问"某个对象"时读出 vftable=0xA8 的假指针崩溃。
		pushad
		mov ecx, s_reanim
		mov eax, s_name
		push s_image
		mov ebx, 0x473490
		call ebx            // ret 4（自带栈清理 image 参数）
		popad
	}
}

// ==================== 豌豆射手 5 阶「骑士」皮肤 ====================
// 目标 reanim = PeaShooterSingle.reanim（豌豆射手 SeedType 0 / AnimType 4；PeaShooter.reanim 是双发射手）。
// 该文件需先跑「豌豆射手5阶皮肤\patch_reanim.py --apply」追加 2 条轨道（原 18 条逐字节未动）：
//   PST5_HEAD  帧 29~103 逐帧复刻 anim_face 的 x/y/sx/sy，但 x'=x-30*sx、y'=y-31*sy
//              （5 阶头贴图把"原版头"画在自己的 (30,31)，减掉它头核心才回到原位置）
//   PST5_BODY  常量 x=-3.2 y=84.4（贴图 76x46），放轨道表最后 = 画在最上层（披风压头，按设计图）
// tier>=5：PST5_* 换新贴图并显示；藏 anim_face（原版头）+ stalk_top/stalk_bottom（茎）。
//          ★ 只藏茎、不藏底部叶片（用户指定）；嘴/眨眼保持原版，新头图只顶替"头"这一颗颗粒。
//          ★ 隐藏手段 = 把该轨道 override 成 1x1 全透明图（**不是**渲染分组 -1，见上面说明）。
// tier<5 ：PST5_* override 成透明图 → 视觉上完全等于原版；**一个原版轨道都不碰**。
// 兜底：轨道不存在（未打 reanim 补丁）、实例数组未建立、贴图没加载出来时一律不动原版，
//       而且 SetImageOverride 之前必须先确认轨道存在（FindTrackIndex 返回 -1 时写入会越界）。
// 贴图槽位：0=T5 头 1=T5 躯干 2=1x1 全透明（隐藏用）
static DWORD g_pst5SkinImg[3] = { 0, 0, 0 };
static bool  g_pst5SkinImgLoaded = false;        // 贴图加载标志（主循环首次执行时加载）
static int   g_pst5SkinImgTries = 0;             // 尝试次数（超上限放弃，避免每帧重复 IO）
// ★ 帧内禁 CRT：轨道存在性缓存必须用定长数组（原来的 std::map 会在帧内 insert 做堆分配）
static const int PST5_CACHE_MAX = 16;
static DWORD g_pst5CacheKey[PST5_CACHE_MAX] = { 0 };
static BYTE  g_pst5CacheVal[PST5_CACHE_MAX] = { 0 };
static int   g_pst5CacheN = 0;
static int   g_pst5DiagN = 0;                    // 诊断日志条数上限（写 D:\pvz_crash.log）

static void LoadPeaShooterT5SkinImages()
{
	__try
	{
		static const char* kFiles[3] = {
			"reanim\\PeaShooterT5_head.png",
			"reanim\\PeaShooterT5_body.png",
			"reanim\\PeaShooterT5_blank.png",   // 1x1 全透明：用来"隐藏"轨道
		};
		static const char* kFilesFwd[3] = {
			"reanim/PeaShooterT5_head.png",
			"reanim/PeaShooterT5_body.png",
			"reanim/PeaShooterT5_blank.png",
		};
		for (int i = 0; i < 3; i++)
		{
			if (g_pst5SkinImg[i] != 0)
				continue;
			Draw::PString filename = Draw::ToString(kFiles[i]);
			Draw::PString variant = Draw::ToString("");
			DWORD isNew = 0;
			DWORD sharedImg = Draw::GetSharedImage(isNew, variant, filename);
			if (sharedImg == 0)
			{
				Draw::PString filename2 = Draw::ToString(kFilesFwd[i]);
				sharedImg = Draw::GetSharedImage(isNew, variant, filename2);
			}
			if (sharedImg != 0)
				g_pst5SkinImg[i] = Draw::SharedImageRefToImage(sharedImg);
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_pst5SkinImgLoaded = false;   // 资源系统未就绪等异常：保持未加载，下帧重试
	}
}

// ★★ 为什么不再用「渲染分组隐藏轨道」(0x473A40 传 -1)：
//   实测（离线渲染游戏里那份 .compiled + 用户游戏截图双重印证）——**对植物无效**：
//   该函数确实把轨道实例 +0x48 写成了 -1（诊断日志回读 rgHead=0xFFFFFFFF 证实写入成功），
//   但植物绘制路径根本不读 +0x48，于是 PST5_HEAD/PST5_BODY 照画不误：
//     · PST5_HEAD 把「原版头」贴图按 x-30sx / y-31sy 画出来 → 屏幕上多一个偏左上方的头
//     · PST5_BODY 把「原版头」贴图按 (-3.2, 84.4) 画出来 → 底下一个大头
//   用户截图里那只"两个头 + 底下一个大头"的豌豆射手就是这个。
//   → 改用本项目已跑通 4 次（花盆装水 / 防爆门 / 冰火 / 金盏花）的**贴图覆盖**机制：
//     把不需要的轨道 override 成 1x1 全透明图，绘制时画一个透明像素 = 视觉隐藏。100% 有效。
//     参考：Pot_top2 = SetImageOverride("Pot_top", img) 的写法。

// 按名字查轨道索引（**纯内存读**，复刻 0x472F30 的遍历逻辑，但完全不调用游戏函数）：
//   reanim + 0x0C -> {nameArray*, count}；nameArray[i] 指向 0xC 字节项，其首字段是名字指针
// 返回索引；-1 = 不存在。
// ★ 为什么不用框架 Animation::FindTrackIndex：它走 Memory::Execute（在共享缓冲区里拼代码执行），
//   每帧路径上代价高且有寄存器保护风险；纯读内存可放心每帧调用（MemSafeRead 自带 VirtualQuery 缓存）。
static int ReanimTrackIndex(DWORD reanimAddr, const char* trackName)
{
	if (reanimAddr < 0x10000 || !trackName) return -1;
	int defTbl = MemSafeRead<int>(reanimAddr + 0x0C);
	if (defTbl < 0x10000) return -1;
	int nameArr = MemSafeRead<int>(defTbl + 0x00);
	int count   = MemSafeRead<int>(defTbl + 0x04);
	if (nameArr < 0x10000 || count <= 0 || count > 512) return -1;
	for (int i = 0; i < count; i++)
	{
		int p = MemSafeRead<int>(nameArr + i * 0x0C);
		if (p < 0x10000) continue;
		int k = 0;
		for (; trackName[k]; k++)
		{
			char c = (char)MemSafeRead<unsigned char>(p + k);
			if (c != trackName[k]) break;
		}
		if (!trackName[k]) return i;          // 完全匹配（含结尾 '\0'）
	}
	return -1;
}

// 本 reanim 是否已打 reanim 补丁（两条皮肤轨道都在）。返回 0 时本段彻底不动原版。
static BYTE PeaShooterT5QueryTracks(DWORD reanimAddr)
{
	// ★ 双保险：reanim 对象必须在**可写的游戏堆**上。exe 镜像基址(0x400000=INVALID_BASEADDRESS)
	//   是 PAGE_EXECUTE_READ，直接否决——这是冰火 GetProjectileFireTrackAnim 用过的同款安全网。
	if (!CrashIsWritable(reanimAddr, 0x60)) return 0;
	if (ReanimTrackIndex(reanimAddr, "PST5_HEAD") < 0) return 0;
	if (ReanimTrackIndex(reanimAddr, "PST5_BODY") < 0) return 0;
	return 1;
}

// 带定长缓存的查询（每 reanim 只现场查一次；缓存满后不再新增，退化为每次都查——只读，安全）
// ★ 2026-10-16：本函数返回 0/1，配合 CrashIsWritable 一起用；注意框架 FindTrackIndex
//   **找不到时返回 0**（不是负数），所以判断"轨道是否存在"一律用本函数（返回 -1）。
static BYTE PeaShooterT5TrackState(DWORD reanimAddr)
{
	for (int i = 0; i < g_pst5CacheN; i++)
		if (g_pst5CacheKey[i] == reanimAddr) return g_pst5CacheVal[i];
	BYTE v = PeaShooterT5QueryTracks(reanimAddr);
	if (g_pst5CacheN < PST5_CACHE_MAX)
	{
		g_pst5CacheKey[g_pst5CacheN] = reanimAddr;
		g_pst5CacheVal[g_pst5CacheN] = v;
		g_pst5CacheN++;
	}
	return v;
}

// 读某条轨道的 override 图（轨道实例 +0x44）。读不到返回 0（= 需要写入）。
static DWORD PeaShooterT5ReadOverride(DWORD inst, int idx)
{
	if (inst < 0x10000 || idx < 0) return 0;
	return MemSafeRead<DWORD>(inst + (DWORD)idx * 0x60 + 0x44);
}

// ── 动画 ID → 0xA0 池对象（Reanimator）解析 ─────────────────────────────
// 反汇编实证（0x472E40 = Reanimator::Draw(Graphics*, int renderGroup)：
//   mov esi,[edi+0x74] / lea ebx,[edi+0x78]（6 个）→ 逐个解析成池对象后调用 Draw）：
//   pool = [[[0x6A9EC0]+0x820]+8]+0 ；对象地址 = pool + (id & 0xFFFF) * 0xA0
//   这与 PVZClass `Animation::Animation()` 的解析链一模一样（框架已在本项目大量验证）。
// 用途：把"帧首登记的豌豆射手 reanim"顺带登记它的关联对象，供绘制期钩子命中。
static DWORD Pst5AnimPoolBase()
{
	int app = MemSafeRead<int>(0x6A9EC0);
	if (app < 0x10000) return 0;
	int w1 = MemSafeRead<int>(app + 0x820);
	if (w1 < 0x10000) return 0;
	int w2 = MemSafeRead<int>(w1 + 8);
	if (w2 < 0x10000) return 0;
	int base = MemSafeRead<int>(w2);
	if (base < 0x10000) return 0;
	return (DWORD)base;
}
static DWORD Pst5AnimFromId(int id)
{
	int idx = id & 0xFFFF;
	if (idx <= 0 || idx > 8192) return 0;
	DWORD base = Pst5AnimPoolBase();
	if (!base) return 0;
	DWORD obj = base + (DWORD)idx * 0xA0;
	if (!CrashIsWritable(obj, 0xA0)) return 0;
	return obj;
}

// ── v7：绘制期换皮（Reanimator::Draw 钩子）──────────────────────────────
// ★ 为什么必须换到绘制期：
//   在 onGameObjectsUpdate（帧首）写 SetImageOverride(0x473490) 后，日志回读轨道实例
//   +0x44 确实是目标图（写入成功），但屏幕上 PST5_HEAD/PST5_BODY 照画占位图 ——
//   即"我们写的实例数组"不是"被绘制的那份"。
// ★ 反汇编实证（0x472E40 = Reanimator::Draw(Graphics* g, int renderGroup)）：
//     for (i = 0; i < [reanim+0xC].count; i++) {
//         inst = [reanim+0x58] + i*0x60;
//         if (inst[0x48] != renderGroup) continue;      // 渲染组过滤（-1 永不绘制）
//         DrawTrack(this, i, ...);                       // 0x4723B0
//     }
//   0x4723B0 内部确实把 inst[0x44] 当贴图覆盖用（0x7269E 判定 + 0x72946 取值）。
//   → override 机制有效；问题在"写到了哪个对象"。
// ★ 方案：钩住 Reanimator::Draw 入口（ecx = 游戏自己传进去、马上要被绘制的那个 reanim），
//   在它遍历轨道之前，对**这个对象**写覆盖。目标由构造保证正确，时序上也无从被改回。
static const int PST5_DRAWCACHE_N = 64;
struct Pst5DrawCache
{
	DWORD reanim;      // 0 = 空槽
	int   head;        // -1 = 无（非本方 reanim）
	int   body;
	int   stalk[2];    // -2 = 未解析；-1 = 无该轨道
};
static Pst5DrawCache g_pst5DCache[PST5_DRAWCACHE_N] = { {0, 0, 0, {0, 0}} };

// 该 reanim 是否带我们的两条轨道（并给出索引）。
// ★ 绘制期每帧每个 reanim 都会问一次 → 必须廉价：哈希槽一读一比较即返回，
//   只有槽位不匹配时才真的按名字查（每个地址一辈子只查一次）。
static BYTE Pst5TracksCached(DWORD reanim, int* outHead, int* outBody)
{
	Pst5DrawCache& e = g_pst5DCache[(reanim >> 4) & (DWORD)(PST5_DRAWCACHE_N - 1)];
	if (e.reanim != reanim)
	{
		e.reanim = reanim;
		e.head = -1; e.body = -1; e.stalk[0] = -2; e.stalk[1] = -2;
		if (CrashIsWritable(reanim, 0x60))
		{
			e.head = ReanimTrackIndex(reanim, "PST5_HEAD");
			if (e.head >= 0) e.body = ReanimTrackIndex(reanim, "PST5_BODY");
			if (e.body < 0) { e.head = -1; e.body = -1; }
		}
	}
	if (e.head < 0) return 0;
	*outHead = e.head;
	*outBody = e.body;
	return 1;
}
// 茎轨道索引（只在 tier≥5 需要 → 惰性解析并缓存）
static int Pst5StalkCached(DWORD reanim, int which)
{
	Pst5DrawCache& e = g_pst5DCache[(reanim >> 4) & (DWORD)(PST5_DRAWCACHE_N - 1)];
	if (e.reanim != reanim) return -1;
	if (e.stalk[which] == -2)
		e.stalk[which] = ReanimTrackIndex(reanim, which == 0 ? "stalk_top" : "stalk_bottom");
	return e.stalk[which];
}

// 帧首登记表：本帧"哪个 reanim 属于哪一等阶的豌豆射手"（供绘制钩子反查等阶）
static DWORD g_pst5TierAnim[24] = { 0 };
static int   g_pst5TierVal[24] = { 0 };
static int   g_pst5TierN = 0;
static int   g_pst5DrawDiagN = 0;

static void Pst5RegisterTier(DWORD reanim, int tier)
{
	if (reanim < 0x10000 || reanim == 0x400000 || reanim >= 0x80000000) return;
	for (int i = 0; i < g_pst5TierN; i++)
	{
		if (g_pst5TierAnim[i] == reanim) { g_pst5TierVal[i] = tier; return; }
	}
	if (g_pst5TierN < 24)
	{
		g_pst5TierAnim[g_pst5TierN] = reanim;
		g_pst5TierVal[g_pst5TierN] = tier;
		g_pst5TierN++;
	}
}
static int Pst5TierForReanim(DWORD reanim)
{
	for (int i = 0; i < g_pst5TierN; i++)
		if (g_pst5TierAnim[i] == reanim) return g_pst5TierVal[i];
	return -1;
}

// 前置声明：向日葵 3 阶皮肤复用同一个绘制钩子（实现在豌豆射手段之后）
static void Sunf3OnDrawReanim(DWORD reanim);

// Reanimator::Draw 入口回调（ecx = 正在被绘制的 reanim，由汇编 trampoline 传入）
static void __cdecl Pst5OnDrawReanim(DWORD reanim)
{
	__try
	{
		// 向日葵 3 阶皮肤：同一个绘制钩子里顺带处理（自带独立的开关与命中判断，互不干扰）
		Sunf3OnDrawReanim(reanim);
		if (!g_pst5SkinEnabled) return;
		if (reanim < 0x10000 || reanim == 0x400000 || reanim >= 0x80000000) return;
		int iHead = -1, iBody = -1;
		if (!Pst5TracksCached(reanim, &iHead, &iBody)) return;   // 其余 reanim 在这里退出（极廉价）

		int tier = Pst5TierForReanim(reanim);           // 帧首登记（≤24 条线性扫）
		if (tier < 0)
		{
			// ★ 关键诊断：被绘制的对象有我们的轨道、但帧首登记的不是它
			//   → 证实"帧首拿到的 reanim ≠ 绘制用的 reanim"。
			if (g_pst5DrawDiagN < 12)
			{
				g_pst5DrawDiagN++;
				CrashStr("\r\n[T5SKIN] draw-nomap\r\n");
				CrashLineHex("drawn", reanim);
				CrashLineHex("tierN", (DWORD)g_pst5TierN);
				for (int k = 0; k < g_pst5TierN && k < 4; k++)
				{
					CrashLineHex("mapAnim", g_pst5TierAnim[k]);
					CrashLineHex("mapTier", (DWORD)g_pst5TierVal[k]);
				}
			}
			return;
		}

		DWORD inst = MemSafeRead<DWORD>(reanim + 0x58);
		if (inst < 0x10000) return;
		int maxIdx = iBody > 2 ? iBody : 2;
		if (!CrashIsWritable(inst, (DWORD)(maxIdx + 1) * 0x60)) return;

		bool haveImg = (g_pst5SkinImg[0] != 0 && g_pst5SkinImg[1] != 0 && g_pst5SkinImg[2] != 0);
		bool skin = (tier >= 5) && haveImg;
		DWORD blank = g_pst5SkinImg[2];
		DWORD wantHead = skin ? g_pst5SkinImg[0] : blank;
		DWORD wantBody = skin ? g_pst5SkinImg[1] : blank;

		if (PeaShooterT5ReadOverride(inst, iHead) != wantHead)
		{
			CRASH_STEP("peashooter:t5skin:draw:ovHead");
			ReanimSetImageOverride(reanim, "PST5_HEAD", wantHead);
		}
		if (PeaShooterT5ReadOverride(inst, iBody) != wantBody)
		{
			CRASH_STEP("peashooter:t5skin:draw:ovBody");
			ReanimSetImageOverride(reanim, "PST5_BODY", wantBody);
		}
		if (skin)
		{
			static const char* kHide[2] = { "stalk_top", "stalk_bottom" };
			for (int i = 0; i < 2; i++)
			{
				int idx = Pst5StalkCached(reanim, i);
				if (idx < 0) continue;
				if (PeaShooterT5ReadOverride(inst, idx) == blank) continue;
				CRASH_STEP("peashooter:t5skin:draw:hideOrig");
				ReanimSetImageOverride(reanim, kHide[i], blank);
			}
		}
		if (g_pst5DrawDiagN < 12)
		{
			g_pst5DrawDiagN++;
			CrashStr("\r\n[T5SKIN] draw\r\n");
			CrashLineHex("drawn", reanim);
			CrashLineHex("tier", (DWORD)tier);
			CrashLineHex("skin", (DWORD)(skin ? 1 : 0));
			CrashLineHex("inst", inst);
			CrashLineHex("idxHead", (DWORD)iHead);
			CrashLineHex("idxBody", (DWORD)iBody);
			CrashLineHex("ovHead", PeaShooterT5ReadOverride(inst, iHead));
			CrashLineHex("ovBody", PeaShooterT5ReadOverride(inst, iBody));
			CrashLineHex("map0", g_pst5TierN > 0 ? g_pst5TierAnim[0] : 0);
		}
	}
	__except (CrashSwallowFilter(GetExceptionInformation()))
	{
	}
}

// 安装 Reanimator::Draw(0x472E40) 入口钩子。
// 原序言 6 字节 = "55 8B EC 83 E4 F8"（push ebp / mov ebp,esp / and esp,-8），
// trampoline 先原样执行这 3 条（保住 ebp=本函数帧指针的语义），再保存 eax/ecx/edx
// （ebx/esi/edi/ebp 由 cdecl 被调方保存），传 ecx 给 C 回调，最后跳回 0x472E46。
static bool g_pst5DrawHookInstalled = false;
static int  g_pst5DrawHookTries = 0;
static bool InstallPst5DrawHook()
{
	if (g_pst5DrawHookInstalled) return true;
	if (g_pst5DrawHookTries >= 3) return false;   // ★ 上限：失败重试也要封顶，否则每帧 VirtualAlloc 漏 4KB
	g_pst5DrawHookTries++;
	const DWORD kSite = 0x472E40;                  // Reanimator::Draw(Graphics* g, int renderGroup)
	const int   kRaw = 6;
	BYTE rawCode[8];
	PVZ::Memory::ReadArray<BYTE>(kSite, rawCode, kRaw);
	{
		static const BYTE kExpected[kRaw] = { 0x55, 0x8B, 0xEC, 0x83, 0xE4, 0xF8 };
		if (memcmp(rawCode, kExpected, kRaw) != 0)
		{
			CrashStr("HOOKFAIL name=Pst5Draw site=0x472E40 (bytes changed)\r\n");
			return false;
		}
	}
	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
	{
		CrashStr("HOOKFAIL name=Pst5Draw (no trampoline)\r\n");
		return false;
	}
	BYTE tp[64];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x55;                                   // push ebp        （原序言）
	tp[p++] = 0x8B; tp[p++] = 0xEC;                    // mov ebp, esp
	tp[p++] = 0x83; tp[p++] = 0xE4; tp[p++] = 0xF8;    // and esp, 0FFFFFFF8h
	tp[p++] = 0x50;                                   // push eax
	tp[p++] = 0x51;                                   // push ecx
	tp[p++] = 0x52;                                   // push edx
	tp[p++] = 0x51;                                   // push ecx（参数 = 正在绘制的 reanim）
	putRelCall((DWORD)&Pst5OnDrawReanim);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;    // add esp, 4
	tp[p++] = 0x5A;                                   // pop edx
	tp[p++] = 0x59;                                   // pop ecx
	tp[p++] = 0x58;                                   // pop eax
	putRelJmp(kSite + kRaw);                          // 回原函数 0x472E46

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);

	BYTE hook[5] = { 0xE9 };
	int rel = (int)((DWORD)tramp - (kSite + 5));
	memcpy(hook + 1, &rel, 4);
	PVZ::Memory::WriteArray<BYTE>(kSite, hook, 5);

	// 回读校验（同 InstallBlastFreedPlantTailGuard 的做法：装完必须读回确认）
	BYTE chk[5];
	PVZ::Memory::ReadArray<BYTE>(kSite, chk, 5);
	if (chk[0] != 0xE9 || memcmp(chk + 1, hook + 1, 4) != 0)
	{
		CrashStr("HOOKFAIL name=Pst5Draw (verify failed) site=0x472E40\r\n");
		return false;
	}
	g_pst5DrawHookInstalled = true;
	CrashStr("[T5SKIN] draw hook installed site=0x472E40\r\n");
	return true;
}

// 实际换皮（无 __try，可含局部对象；被 PeaShooterT5SkinFrame 的 __try 包裹）
static void PeaShooterT5ApplyInner(int plantAddr)
{
	// ★ 只藏两根茎（用户指定：不藏底部叶片）。
	//   **不藏 anim_face**：新头贴图是"原版头 1:1 顶替件"（原版 PeaShooter_Head.png 70×65
	//   正好落在新图 (30,31)，alpha 掩码覆盖率 1.0000）→ 天然盖住原版头，嘴/眨眼按设计保留。
	//   PST5_HEAD 在轨道表里就排在 anim_face 之后（文件补丁保证），层序天然正确。
	static const char* kHideInSkin[2] = { "stalk_top", "stalk_bottom" };

	PVZ::Plant plant(plantAddr);
	PVZ::Animation anim = plant.GetAnimationPart1();
	// ★★ 关键防护：取不到动画时 GetAnimationPart1() 返回 INVALID_BASEADDRESS = 0x400000，
	//    而那是 **exe 的镜像基址、完全合法可读** —— 用 !reanim 拦不住（0x400000 != 0）。
	//    种植瞬间动画尚未建立，若把它当 reanim 用，就会拿 PE 头当轨道表遍历 → 乱写内存 → 崩。
	DWORD reanim = (DWORD)anim.GetBaseAddress();
	if (reanim < 0x10000 || reanim == 0x400000 || reanim >= 0x80000000) return;

	int exp = 0;
	auto it = g_plantExperience.find(plantAddr);
	if (it != g_plantExperience.end()) exp = it->second;
	int tier = GetPlantTier((int)SeedType::Peashooter, exp);

	// ★ 轨道必须存在，否则 SetImageOverride 内部 FindTrackIndex 返回 -1 会拿 idx*0x60 去越界写
	//   → 写到实例数组前面 0x60 字节处 = 堆损坏 = 随机延迟崩溃。这是本段最危险的一条，绝不放行。
	if (!PeaShooterT5TrackState(reanim)) return;

	// ★ 轨道实例数组必须已经建立。种植瞬间 [reanim+0x58] 可能是 0，
	//   此时任何 SetImageOverride 都会写到低位地址 → 立刻 AV。
	DWORD inst = MemSafeRead<DWORD>(reanim + 0x58);
	if (inst < 0x10000) return;

	int iHead = ReanimTrackIndex(reanim, "PST5_HEAD");
	int iBody = ReanimTrackIndex(reanim, "PST5_BODY");
	if (iHead < 0 || iBody < 0) return;
	// ★ 整段实例数组必须可写（冰火 GetProjectileFireTrackAnim 同款安全网）
	int maxIdx = iBody > 2 ? iBody : 2;
	if (!CrashIsWritable(inst, (DWORD)(maxIdx + 1) * 0x60)) return;

	bool haveImg = (g_pst5SkinImg[0] != 0 && g_pst5SkinImg[1] != 0 && g_pst5SkinImg[2] != 0);
	bool skin = (tier >= 5) && haveImg;

	DWORD blank = g_pst5SkinImg[2];
	DWORD wantHead = skin ? g_pst5SkinImg[0] : blank;
	DWORD wantBody = skin ? g_pst5SkinImg[1] : blank;

	// ★ 幂等做法：先读回当前 override，已是目标值就一个字节都不写。
	//   好处：① 常态下本段每帧零写入、几乎零开销 ② 动画实例被游戏重建/内存池复用时自动重新生效
	//   （不做"上次应用过"的地址缓存 —— 池复用会让地址缓存骗过我们，导致皮肤突然消失）
	CRASH_STEP("peashooter:t5skin:apply");
	if (PeaShooterT5ReadOverride(inst, iHead) != wantHead)
	{
		CRASH_STEP("peashooter:t5skin:ovHead");
		ReanimSetImageOverride(reanim, "PST5_HEAD", wantHead);
	}
	if (PeaShooterT5ReadOverride(inst, iBody) != wantBody)
	{
		CRASH_STEP("peashooter:t5skin:ovBody");
		ReanimSetImageOverride(reanim, "PST5_BODY", wantBody);
	}
	if (skin)
	{
		// 藏两根茎（用户指定：不藏底部叶片）。用 1x1 透明图覆盖 = 视觉隐藏。
		for (int i = 0; i < 2; i++)
		{
			int idx = ReanimTrackIndex(reanim, kHideInSkin[i]);
			if (idx < 0) continue;
			if (PeaShooterT5ReadOverride(inst, idx) == blank) continue;
			CRASH_STEP("peashooter:t5skin:hideOrig");
			ReanimSetImageOverride(reanim, kHideInSkin[i], blank);
		}
	}

	// 一次性诊断（写 D:\pvz_crash.log）：回读轨道实例 +0x44(override 图)
	// ★ 对比关键点：把"本段拿到的 reanim（= plant.GetAnimationPart1()）"和
	//   "绘制期真正被绘制的那个 reanim（Draw 钩子里的 link/preanim）"都打出来，
	//   一眼能看出两者是否同一个对象 —— 这决定了覆盖到底写没写在被绘制的实例上。
	if (g_pst5DiagN < 6)
	{
		g_pst5DiagN++;
		CrashStr("\r\n[T5SKIN] apply\r\n");
		CrashLineHex("plant", (DWORD)plantAddr);
		CrashLineHex("reanimPart1", reanim);
		CrashLineHex("tier", (DWORD)tier);
		CrashLineHex("skin", (DWORD)(skin ? 1 : 0));
		CrashLineHex("imgHead", g_pst5SkinImg[0]);
		CrashLineHex("imgBody", g_pst5SkinImg[1]);
		CrashLineHex("imgBlank", g_pst5SkinImg[2]);
		CrashLineHex("idxHead", (DWORD)iHead);
		CrashLineHex("idxBody", (DWORD)iBody);
		CrashLineHex("idxFace", (DWORD)ReanimTrackIndex(reanim, "anim_face"));
		CrashLineHex("inst", inst);
		CrashLineHex("ovHead", PeaShooterT5ReadOverride(inst, iHead));
		CrashLineHex("ovBody", PeaShooterT5ReadOverride(inst, iBody));
		CrashLineHex("ovFace", PeaShooterT5ReadOverride(inst, ReanimTrackIndex(reanim, "anim_face")));
	}
}

// 每帧给 5 阶豌豆射手换皮（幂等；动画实例重建后自动重新生效）
// ★ 直接用 MemSafeRead 遍历植物数组，不再用 Board::GetAllPlants()：
//   后者每帧构造 std::vector（CRT 堆分配 + 析构），违反"帧内禁 CRT"铁律，
//   而且会在游戏堆上制造无谓的分配活动 —— 排查"种植瞬间崩溃"时这是首要嫌疑。
static int g_pst5FrameTick = 0;
static void PeaShooterT5SkinFrameInner(DWORD boardAddress)
{
	g_pst5TierN = 0;                                         // 重建本帧登记表
	if (!g_pst5SkinEnabled) return;                          // ini 开关：0 = 整段跳过
	int cnt = MemSafeRead<int>((int)boardAddress + 0xB0);    // 植物数量
	int arr = MemSafeRead<int>((int)boardAddress + 0xAC);    // 植物数组基址
	if (arr < 0x10000 || cnt <= 0 || cnt > 2048) return;

	// 心跳日志：确认本段每帧确实在跑（每 600 帧一条，最多 8 条）
	g_pst5FrameTick++;
	if (g_pst5FrameTick % 600 == 1 && g_pst5FrameTick <= 4801)
	{
		CrashStr("\r\n[T5SKIN] tick\r\n");
		CrashLineHex("tick", (DWORD)g_pst5FrameTick);
		CrashLineHex("enabled", (DWORD)g_pst5SkinEnabled);
		CrashLineHex("plants", (DWORD)cnt);
		CrashLineHex("imgHead", g_pst5SkinImg[0]);
		CrashLineHex("imgBody", g_pst5SkinImg[1]);
		CrashLineHex("imgBlank", g_pst5SkinImg[2]);
	}

	for (int i = 0; i < cnt; i++)
	{
		int p = arr + 0x14C * i;
		if (MemSafeRead<BYTE>(p + 0x141)) continue;               // NotExist
		if (MemSafeRead<int>(p + 0x24) != (int)SeedType::Peashooter) continue;
		PeaShooterT5ApplyInner(p);
		// ★ 帧首登记：把这只豌豆射手的"等阶"挂到它的若干候选 reanim 对象上，
		//   供绘制期钩子（Reanimator::Draw）反查等阶用（见 Pst5OnDrawReanim）。
		//   绘制钩子里会先确认该对象确实有 PST5_HEAD/PST5_BODY 轨道才会写覆盖
		//   → 登记到"没有这两条轨道的对象"上完全无害（顶多白查一次）。
		//   ★ 注意：**不要**用 [reanim+0x74] 去推关联对象——对 Reanimator 来说 +0x74
		//   是加色蓝分量（0x6C..0x78 是颜色），硬按动画 ID 解释会解析到别的植物身上，
		//   反而可能把别株的等阶写串。
		{
			PVZ::Plant pl(p);
			DWORD a1 = (DWORD)pl.GetAnimationPart1().GetBaseAddress();
			int exp = 0;
			auto it = g_plantExperience.find(p);
			if (it != g_plantExperience.end()) exp = it->second;
			int tier = GetPlantTier((int)SeedType::Peashooter, exp);
			Pst5RegisterTier(a1, tier);
			Pst5RegisterTier((DWORD)pl.GetAnimationPart2().GetBaseAddress(), tier);
			Pst5RegisterTier((DWORD)pl.GetAnimationPart3().GetBaseAddress(), tier);
			Pst5RegisterTier((DWORD)pl.GetAnimationPart4().GetBaseAddress(), tier);
		}
	}
}

static void PeaShooterT5SkinFrame(DWORD boardAddress)
{
	__try
	{
		PeaShooterT5SkinFrameInner(boardAddress);
	}
	// ★ 不能再用裸 EXCEPTION_EXECUTE_HANDLER 静默吞：万一本段抛异常，日志里会留下
	//   "CRASH (SWALLOW) step=peashooter:t5skin*" → 一眼看出是这段哪一步出的问题。
	__except (CrashSwallowFilter(GetExceptionInformation()))
	{
	}
}

// ==================== 向日葵 3 阶「皇冠 + 权杖」皮肤 ====================
// 目标 reanim = SunFlower.reanim（向日葵 SeedType 1）。
// 该文件需先跑「向日葵3阶皮肤\patch_sunflower_skin.py --apply」追加 2 条轨道（原 29 条逐字节未动）：
//   SUNF3_HEAD    插在 anim_idle(原版脸) 之后、anim_blink(眨眼) 之前；
//                 逐帧复刻 anim_idle 的 x/y/sx/sy，但 x'=x-1*sx、y'=y-22*sy
//                 （新头 58x65 把原版脸 57x43 1:1 画在自己的 (1,22)，alpha 掩码覆盖率 1.0000
//                  → 天然盖住原头，眨眼轨道仍在它上面，嘴/眼按设计保留）
//   SUNF3_SCEPTER 放轨道表最后（= 最上层，压在花瓣/叶子上）；
//                 自带摇摆：基准 + 0.6×(头的位移) + 椭圆漂移（不照抄头的运动）
// tier>=3：两条轨道换成新贴图；tier<3：override 成 1x1 全透明 → 视觉上完全等于原版。
// 兜底：reanim 指针取不到时 GetAnimationPart1() 会返回 INVALID_BASEADDRESS=0x400000（合法可读！）
//       → 必须显式拦截；轨道不存在 / 实例数组未建立 / 贴图未加载时一律不动原版。
static DWORD g_sunf3Img[3] = { 0, 0, 0 };        // 0=皇冠头 1=权杖 2=1x1 全透明（回滚/隐藏用）
static bool  g_sunf3ImgLoaded = false;
static int   g_sunf3ImgTries = 0;
static const int SUNF3_CACHE_N = 64;
struct Sunf3DrawCache { DWORD reanim; int head; int scep; };
static Sunf3DrawCache g_sunf3DCache[SUNF3_CACHE_N] = { {0, -1, -1} };
static DWORD g_sunf3TierAnim[24] = { 0 };        // 帧首登记：reanim -> 等阶（供绘制钩子反查）
static int   g_sunf3TierVal[24] = { 0 };
static int   g_sunf3TierN = 0;
static int   g_sunf3DiagN = 0;
static int   g_sunf3DrawDiagN = 0;
static int   g_sunf3FrameTick = 0;

static void LoadSunFlowerT3SkinImages()
{
	__try
	{
		static const char* kFiles[2] = {
			"reanim\\SunFlowerT3_head.png",
			"reanim\\SunFlowerT3_scepter.png",
		};
		static const char* kFilesFwd[2] = {
			"reanim/SunFlowerT3_head.png",
			"reanim/SunFlowerT3_scepter.png",
		};
		for (int i = 0; i < 2; i++)
		{
			if (g_sunf3Img[i] != 0) continue;
			Draw::PString variant = Draw::ToString("");
			DWORD isNew = 0;
			DWORD sharedImg = Draw::GetSharedImage(isNew, variant, Draw::ToString(kFiles[i]));
			if (sharedImg == 0)
				sharedImg = Draw::GetSharedImage(isNew, variant, Draw::ToString(kFilesFwd[i]));
			if (sharedImg != 0)
				g_sunf3Img[i] = Draw::SharedImageRefToImage(sharedImg);
		}
		// 回滚/隐藏用的 1x1 全透明图（复用豌豆射手那份，已存在）
		if (g_sunf3Img[2] == 0)
		{
			Draw::PString variant = Draw::ToString("");
			DWORD isNew = 0;
			DWORD s = Draw::GetSharedImage(isNew, variant, Draw::ToString("reanim\\PeaShooterT5_blank.png"));
			if (s != 0) g_sunf3Img[2] = Draw::SharedImageRefToImage(s);
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_sunf3ImgLoaded = false;   // 资源系统未就绪：保持未加载，下帧重试
	}
}

// 本 reanim 是否已打向日葵皮肤补丁（两条轨道都在）。0 = 本段彻底不动它。
static BYTE Sunf3QueryTracks(DWORD reanimAddr)
{
	if (!CrashIsWritable(reanimAddr, 0x60)) return 0;
	if (ReanimTrackIndex(reanimAddr, "SUNF3_HEAD") < 0) return 0;
	if (ReanimTrackIndex(reanimAddr, "SUNF3_SCEPTER") < 0) return 0;
	return 1;
}

// 绘制期热路径：64 槽哈希缓存，只有地址变化时才按名字现查（每个地址一辈子查一次）
static BYTE Sunf3TracksCached(DWORD reanim, int* outHead, int* outScep)
{
	Sunf3DrawCache& e = g_sunf3DCache[(reanim >> 4) & (DWORD)(SUNF3_CACHE_N - 1)];
	if (e.reanim != reanim)
	{
		e.reanim = reanim; e.head = -1; e.scep = -1;
		if (CrashIsWritable(reanim, 0x60))
		{
			e.head = ReanimTrackIndex(reanim, "SUNF3_HEAD");
			if (e.head >= 0) e.scep = ReanimTrackIndex(reanim, "SUNF3_SCEPTER");
			if (e.scep < 0) { e.head = -1; e.scep = -1; }
		}
	}
	if (e.head < 0) return 0;
	*outHead = e.head; *outScep = e.scep;
	return 1;
}

static void Sunf3RegisterTier(DWORD reanim, int tier)
{
	if (reanim < 0x10000 || reanim == 0x400000 || reanim >= 0x80000000) return;
	for (int i = 0; i < g_sunf3TierN; i++)
		if (g_sunf3TierAnim[i] == reanim) { g_sunf3TierVal[i] = tier; return; }
	if (g_sunf3TierN < 24)
	{
		g_sunf3TierAnim[g_sunf3TierN] = reanim;
		g_sunf3TierVal[g_sunf3TierN] = tier;
		g_sunf3TierN++;
	}
}
static int Sunf3TierForReanim(DWORD reanim)
{
	for (int i = 0; i < g_sunf3TierN; i++)
		if (g_sunf3TierAnim[i] == reanim) return g_sunf3TierVal[i];
	return -1;
}

// 绘制期应用（由 Reanimator::Draw 的同一个 trampoline 顺带调用；ecx = 正在被绘制的 reanim）
static void Sunf3OnDrawReanim(DWORD reanim)
{
	__try
	{
		if (!g_sunf3SkinEnabled) return;
		if (reanim < 0x10000 || reanim == 0x400000 || reanim >= 0x80000000) return;
		int iHead = -1, iScep = -1;
		if (!Sunf3TracksCached(reanim, &iHead, &iScep)) return;   // 其余 reanim 在这里廉价退出
		int tier = Sunf3TierForReanim(reanim);
		if (tier < 0) return;
		DWORD inst = MemSafeRead<DWORD>(reanim + 0x58);
		if (inst < 0x10000) return;
		int maxIdx = iScep > iHead ? iScep : iHead;
		if (!CrashIsWritable(inst, (DWORD)(maxIdx + 1) * 0x60)) return;

		bool haveImg = (g_sunf3Img[0] != 0 && g_sunf3Img[1] != 0 && g_sunf3Img[2] != 0);
		bool skin = (tier >= 3) && haveImg;
		DWORD blank = g_sunf3Img[2];
		DWORD wantHead = skin ? g_sunf3Img[0] : blank;
		DWORD wantScep = skin ? g_sunf3Img[1] : blank;

		if (PeaShooterT5ReadOverride(inst, iHead) != wantHead)
		{
			CRASH_STEP("sunflower:t3skin:draw:ovHead");
			ReanimSetImageOverride(reanim, "SUNF3_HEAD", wantHead);
		}
		if (PeaShooterT5ReadOverride(inst, iScep) != wantScep)
		{
			CRASH_STEP("sunflower:t3skin:draw:ovScep");
			ReanimSetImageOverride(reanim, "SUNF3_SCEPTER", wantScep);
		}
		if (g_sunf3DrawDiagN < 8)
		{
			g_sunf3DrawDiagN++;
			CrashStr("\r\n[SUNF3SKIN] draw\r\n");
			CrashLineHex("drawn", reanim);
			CrashLineHex("tier", (DWORD)tier);
			CrashLineHex("skin", (DWORD)(skin ? 1 : 0));
			CrashLineHex("idxHead", (DWORD)iHead);
			CrashLineHex("idxScep", (DWORD)iScep);
			CrashLineHex("ovHead", PeaShooterT5ReadOverride(inst, iHead));
			CrashLineHex("ovScep", PeaShooterT5ReadOverride(inst, iScep));
		}
	}
	__except (CrashSwallowFilter(GetExceptionInformation()))
	{
	}
}

// 帧首换皮（幂等；与绘制期钩子双保险）
static void SunFlowerT3ApplyInner(int plantAddr)
{
	PVZ::Plant plant(plantAddr);
	PVZ::Animation anim = plant.GetAnimationPart1();
	DWORD reanim = (DWORD)anim.GetBaseAddress();
	// ★★ GetAnimationPart1() 取不到时返回 INVALID_BASEADDRESS = 0x400000 = exe 镜像基址（合法可读）
	if (reanim < 0x10000 || reanim == 0x400000 || reanim >= 0x80000000) return;

	int exp = 0;
	auto it = g_plantExperience.find(plantAddr);
	if (it != g_plantExperience.end()) exp = it->second;
	int tier = GetPlantTier((int)SeedType::Sunflower, exp);

	if (!Sunf3QueryTracks(reanim)) return;
	DWORD inst = MemSafeRead<DWORD>(reanim + 0x58);
	if (inst < 0x10000) return;
	int iHead = ReanimTrackIndex(reanim, "SUNF3_HEAD");
	int iScep = ReanimTrackIndex(reanim, "SUNF3_SCEPTER");
	if (iHead < 0 || iScep < 0) return;
	int maxIdx = iScep > iHead ? iScep : iHead;
	if (!CrashIsWritable(inst, (DWORD)(maxIdx + 1) * 0x60)) return;

	bool haveImg = (g_sunf3Img[0] != 0 && g_sunf3Img[1] != 0 && g_sunf3Img[2] != 0);
	bool skin = (tier >= 3) && haveImg;
	DWORD blank = g_sunf3Img[2];
	DWORD wantHead = skin ? g_sunf3Img[0] : blank;
	DWORD wantScep = skin ? g_sunf3Img[1] : blank;

	CRASH_STEP("sunflower:t3skin:apply");
	if (PeaShooterT5ReadOverride(inst, iHead) != wantHead)
	{
		CRASH_STEP("sunflower:t3skin:ovHead");
		ReanimSetImageOverride(reanim, "SUNF3_HEAD", wantHead);
	}
	if (PeaShooterT5ReadOverride(inst, iScep) != wantScep)
	{
		CRASH_STEP("sunflower:t3skin:ovScep");
		ReanimSetImageOverride(reanim, "SUNF3_SCEPTER", wantScep);
	}
	if (g_sunf3DiagN < 4)
	{
		g_sunf3DiagN++;
		CrashStr("\r\n[SUNF3SKIN] apply\r\n");
		CrashLineHex("plant", (DWORD)plantAddr);
		CrashLineHex("reanimPart1", reanim);
		CrashLineHex("tier", (DWORD)tier);
		CrashLineHex("skin", (DWORD)(skin ? 1 : 0));
		CrashLineHex("imgHead", g_sunf3Img[0]);
		CrashLineHex("imgScep", g_sunf3Img[1]);
		CrashLineHex("imgBlank", g_sunf3Img[2]);
		CrashLineHex("idxHead", (DWORD)iHead);
		CrashLineHex("idxScep", (DWORD)iScep);
		CrashLineHex("inst", inst);
		CrashLineHex("ovHead", PeaShooterT5ReadOverride(inst, iHead));
		CrashLineHex("ovScep", PeaShooterT5ReadOverride(inst, iScep));
	}
}

// 每帧给 3 阶以上向日葵换皮（MemSafeRead 直遍历植物数组，帧内不碰 CRT）
static void SunFlowerT3SkinFrameInner(DWORD boardAddress)
{
	g_sunf3TierN = 0;                                         // 重建本帧登记表
	if (!g_sunf3SkinEnabled) return;
	int cnt = MemSafeRead<int>((int)boardAddress + 0xB0);
	int arr = MemSafeRead<int>((int)boardAddress + 0xAC);
	if (arr < 0x10000 || cnt <= 0 || cnt > 2048) return;

	g_sunf3FrameTick++;
	if (g_sunf3FrameTick % 600 == 1 && g_sunf3FrameTick <= 4801)
	{
		CrashStr("\r\n[SUNF3SKIN] tick\r\n");
		CrashLineHex("tick", (DWORD)g_sunf3FrameTick);
		CrashLineHex("enabled", (DWORD)g_sunf3SkinEnabled);
		CrashLineHex("plants", (DWORD)cnt);
		CrashLineHex("imgHead", g_sunf3Img[0]);
		CrashLineHex("imgScep", g_sunf3Img[1]);
		CrashLineHex("imgBlank", g_sunf3Img[2]);
	}

	for (int i = 0; i < cnt; i++)
	{
		int p = arr + 0x14C * i;
		if (MemSafeRead<BYTE>(p + 0x141)) continue;               // NotExist
		if (MemSafeRead<int>(p + 0x24) != (int)SeedType::Sunflower) continue;
		SunFlowerT3ApplyInner(p);
		// 帧首登记等阶（绘制钩子反查用）。登记到没有我们轨道的对象上完全无害。
		PVZ::Plant pl(p);
		int exp = 0;
		auto it = g_plantExperience.find(p);
		if (it != g_plantExperience.end()) exp = it->second;
		int tier = GetPlantTier((int)SeedType::Sunflower, exp);
		Sunf3RegisterTier((DWORD)pl.GetAnimationPart1().GetBaseAddress(), tier);
		Sunf3RegisterTier((DWORD)pl.GetAnimationPart2().GetBaseAddress(), tier);
		Sunf3RegisterTier((DWORD)pl.GetAnimationPart3().GetBaseAddress(), tier);
		Sunf3RegisterTier((DWORD)pl.GetAnimationPart4().GetBaseAddress(), tier);
	}
}

static void SunFlowerT3SkinFrame(DWORD boardAddress)
{
	__try
	{
		SunFlowerT3SkinFrameInner(boardAddress);
	}
	__except (CrashSwallowFilter(GetExceptionInformation()))
	{
	}
}

// 冰火蓝火贴图加载（onGameObjectsUpdate 首帧一次性，同金盏花 LoadMarigoldImages 模式）
// 加载原版帧图 + 蓝版帧图，填 g_iceFireImgPairs 匹配表（{原版, 蓝版} × 主体+flame1/2/3）
static void LoadIceFireImages()
{
	__try
	{
		DWORD isNew = 0;
		Draw::PString variant = Draw::ToString("");
		struct PairDef { const char* orig; const char* ice; };
		PairDef defs[4] = {
			{ "reanim\\FirePea.png",        "images\\IceFire_Pea_body.png" },
			{ "reanim\\FirePea_flame1.png", "images\\IceFire_Pea_flame1.png" },
			{ "reanim\\FirePea_flame2.png", "images\\IceFire_Pea_flame2.png" },
			{ "reanim\\FirePea_flame3.png", "images\\IceFire_Pea_flame3.png" },
		};
		g_iceFireImgPairCount = 0;
		for (int i = 0; i < 4; i++)
		{
			Draw::PString fo = Draw::ToString(defs[i].orig);
			DWORD ro = Draw::GetSharedImage(isNew, variant, fo);
			Draw::PString fi = Draw::ToString(defs[i].ice);
			DWORD ri = Draw::GetSharedImage(isNew, variant, fi);
			if (ro && ri)
			{
				g_iceFireImgPairs[g_iceFireImgPairCount][0] = Draw::SharedImageRefToImage(ro);
				g_iceFireImgPairs[g_iceFireImgPairCount][1] = Draw::SharedImageRefToImage(ri);
				g_iceFireImgPairCount++;
			}
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 冰火：按帧匹配换图（尾焰动态修复）
// 游戏每帧更新轨道元素 +0x40=当前帧原版图；遍历轨道（0x60/条），匹配到原版 → 写 +0x44=蓝版
// → 绘制用 override 显示蓝版当前帧 → 3 帧火焰动画恢复动态
// 返回是否有匹配（false → 调用方 fallback 静态蓝版，防止完全失去染色）
static bool ApplyIceFireTracks(DWORD animAddr)
{
	if (g_iceFireImgPairCount <= 0 || !animAddr) return false;
	int arr = MemSafeRead<int>(animAddr + 0x58);
	if (arr < 0x10000) return false;
	int defTbl = MemSafeRead<int>(animAddr + 0xC);
	int count = 0;
	if (defTbl >= 0x10000)
	{
		int c = MemSafeRead<int>(defTbl + 4);
		if (c > 0 && c <= 32) count = c;
	}
	if (count <= 0) return false;
	bool matched = false;
	for (int i = 0; i < count; i++)
	{
		int elem = arr + i * 0x60;
		if (elem < 0x100000) continue;
		int img = MemSafeRead<int>(elem + 0x40);
		if (img < 0x10000) continue;
		for (int k = 0; k < g_iceFireImgPairCount; k++)
		{
			if (img == (int)g_iceFireImgPairs[k][0])
			{
				MemSafeWrite<int>(elem + 0x44, (int)g_iceFireImgPairs[k][1]);
				matched = true;
				break;
			}
		}
	}
	return matched;
}

// 豌豆染色每帧轮询 Inner（无 __try——内部含 vector 需析构，与剧毒同模式）
static void ApplyPeaTintFrameInner(DWORD boardAddress)
{
	// 解锁 reanim 全局取色（同剧毒机制）：0x52D3EA 改 jmp 后 reanim 绘制读对象 +0x48 颜色
	// ★ 闪白诊断期跳过（诊断需要原版着色代码上锁运行，捕获其真实写入）
	if (g_flashDiagDone)
		SafeUnlockZombieColor();

	PVZ::Board board(boardAddress);
	if (!board.GetBaseAddress()) return;
	auto projs = board.GetAllProjectile();
	for (auto& p : projs)
	{
		if (p.NotExist) continue;
		if ((int)p.Type != (int)ProjectileType::FirePea) continue;
		DWORD pa = p.GetBaseAddress();
		if (!pa) continue;
		int mark = MemSafeRead<int>(pa + 0x8C);
		if (mark < 1 || mark > 3) continue;
		DWORD anim = GetProjectileFireTrackAnim(pa);
		if (!anim) continue;
		if (mark == 3)
		{
			// 冰火：蓝火贴图按帧匹配换图（幂等每帧写；乘色无法把橙红火球变蓝，必须换贴图）
			if (!ApplyIceFireTracks(anim))
			{
				// 匹配失败兜底：静态蓝版（flame2 中间帧），火焰静止但保持蓝色
				if (g_iceFireImgPairCount > 2 && g_iceFireImgPairs[2][1])
					ReanimSetImageOverride(anim, "FirePea_flames", g_iceFireImgPairs[2][1]);
				if (g_iceFireImgPairCount > 0 && g_iceFireImgPairs[0][1])
					ReanimSetImageOverride(anim, "FirePea", g_iceFireImgPairs[0][1]);
			}
		}
		else
		{
			// 弱火/炎：乘色可达（贴图橙红 B≈0，tint 调红黄系正好符合暖色需求）
			const int* col = (mark == 1) ? (const int*)&g_peaWeakFireColor : (const int*)&g_peaBlazeColor;
			MemSafeWrite<int>(anim + 0x48, col[0]);
			MemSafeWrite<int>(anim + 0x4C, col[1]);
			MemSafeWrite<int>(anim + 0x50, col[2]);
			MemSafeWrite<int>(anim + 0x54, col[3]);
		}
	}
}

// 豌豆染色每帧轮询入口（__try 外壳：Inner 含 vector 无法自带 __try（C2712））
static void ApplyPeaTintFrame(DWORD boardAddress)
{
	__try
	{
		ApplyPeaTintFrameInner(boardAddress);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_peaTintErr++;   // 排障铁律：空实现是盲区
	}
}

int onProjectileCollision(DWORD projectileAddress)
{
	auto projectile = std::make_shared<PVZ::Projectile>(projectileAddress);
	if (projectile->Type == ProjectileType::Basketball) return 2;
	if (projectile->Type == ProjectileType::ZombiePea) return 1;
	return 0;
}

void onProjectileCreate(DWORD projectileAddress)
{
}

DWORD onProjectileHitPlant(DWORD projectileAddress, DWORD plantAddress)
{
	auto plant = std::make_shared<PVZ::Plant>(plantAddress);
	return plant->GetBaseAddress();
}

// ★ 2026-09-01 火焰特效诊断：读 Reanim 定义表（0x6A9EF0，每项 12 字节）第 0x22(34) 项，
//   写 D:\pvz_fireball_tbl.txt（只写一次，纯 Win32 CreateFileA/WriteFile，禁 CRT 铁律）。
//   依据 0x4735E0 反汇编：0x6A9EE8 表（16字节/项）是运行时缓存，项[0]==0 时从
//   0x6A9EF0 表（12字节/项 = type*3*4）初始化 → 0x6A9EF0 才是 Reanim 定义表。
//   日志文件存在 = FireBallHitEffect 分支确实被调用（顺带验证执行路径）。
static int g_fireTblLogged = 0;
static void LogFireballTableInner()
{
	char buf[1024];
	int p = 0;
	const char* hex = "0123456789ABCDEF";
	DWORD tbl1 = MemSafeRead<int>(0x6A9EE8); // 缓存表（16B/项）
	DWORD tbl2 = MemSafeRead<int>(0x6A9EF0); // 定义表（12B/项）
	auto puthex = [&](DWORD v) { for (int s = 28; s >= 0; s -= 4) buf[p++] = hex[(v >> s) & 0xF]; };
	auto puts = [&](const char* s) { while (*s) buf[p++] = *s++; };
	auto putstrptr = [&](DWORD ptr) {
		if (ptr > 0x10000)
		{
			for (int k = 0; k < 63; k++)
			{
				char ch = MemSafeRead<char>(ptr + k);
				if (ch == 0) break;
				buf[p++] = (ch >= 32 && ch < 127) ? ch : '.';
			}
		}
	};
	puts("tbl1="); puthex(tbl1);
	puts(" tbl2="); puthex(tbl2);
	if (tbl2 >= 0x10000)
	{
		DWORD base = tbl2 + 0x22 * 12; // 第 34 项（12 字节/项）
		DWORD e0 = MemSafeRead<int>(base);
		DWORD e1 = MemSafeRead<int>(base + 4);
		DWORD e2 = MemSafeRead<int>(base + 8);
		puts(" e0="); puthex(e0);
		puts(" e1="); puthex(e1);
		puts(" e2="); puthex(e2);
		puts(" name0="); putstrptr(e0);
		puts(" name1="); putstrptr(e1);
		puts(" name2="); putstrptr(e2);
		if (tbl1 >= 0x10000)
		{
			DWORD c0 = MemSafeRead<int>(tbl1 + 0x22 * 16);
			puts(" cache0="); puthex(c0);
		}
	}
	else
	{
		puts(" (tbl2 invalid)");
	}
	buf[p++] = '\r'; buf[p++] = '\n';
	HANDLE h = CreateFileA("D:\\pvz_fireball_tbl.txt", GENERIC_WRITE, FILE_SHARE_READ,
		NULL, OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
	if (h != INVALID_HANDLE_VALUE)
	{
		SetFilePointer(h, 0, NULL, FILE_BEGIN);
		DWORD w;
		WriteFile(h, buf, (DWORD)p, &w, NULL);
		CloseHandle(h);
	}
}

static void LogFireballTable()
{
	if (g_fireTblLogged) return;
	g_fireTblLogged = 1;
	__try
	{
		LogFireballTableInner();
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ===== 火球命中火焰特效（原版 0x46E25F-0x46E2C5 复刻，0x45xxxx 可信区反汇编）=====
// 原版流程（0x46E000 命中处理，Type 6 分支）：
//   Type 6 火球 → 0x46D1F0 判定（eax=子弹/ecx=僵尸，特判僵尸返回 0）→ al==1 →
//   0x453C30 创建 Reanim 特效（eax=LawnApp([proj+0])、ebx=0x22(type 34)、
//   栈 push render_order=[proj+0x20]+1; X=[proj+0x34]-qword[0x679338];
//   Y=[proj+0x30]+qword[0x67A288]，ret 0xC 清 3 参数）→ 返回对象写 4 字段
//   （[+4]/[+8]/[+0x24]/[+0x34]=全局常量浮点）→ 随后 Remove 子弹
// ★ 这是原版"火豆打在僵尸上的火焰特效"，一次性视觉；原版无染色、无持续伤害。
// ★ float 全在 __asm 内从内存读（MSVC 铁律：跨 __asm 的 float 局部不可靠）
static void FireBallHitEffect(DWORD projAddr, DWORD zombieAddr)
{
	if (!projAddr || !zombieAddr) return;
	LogFireballTable(); // 诊断：type 0x22 动画名（只写一次）
	DWORD lawnApp = MemSafeRead<int>(projAddr + 0); // [proj+0]=LawnApp（GameObject 铁律）
	if (!lawnApp) return;
	__asm {
		// 判定：0x46D1F0(eax=子弹, ecx=僵尸) → al=1 播特效 / 0 不播（特判僵尸）
		// ★★★ MSVC 内联汇编语义陷阱（2026-09-01 实测火焰特效不可见根因）：
		//   [projAddr + 0x34] = "局部变量地址+偏移"（栈寻址 [ebp-4+0x34]），
		//   不是"projAddr 的值+偏移"（子弹+0x34）！变量值必须先 mov 到寄存器。
		//   必须 mov esi, projAddr 后用 [esi+0x34]。0x46D1F0 只用 eax/ecx/edx，esi 安全。
		mov ecx, zombieAddr
		mov eax, projAddr
		mov esi, projAddr
		mov ebx, 0x46D1F0
		call ebx
		test al, al
		je done
		// 特效：0x453C30(eax=LawnApp, ebx=0x22, 栈 push render_order; X; Y, ret 0xC)
		mov eax, lawnApp
		mov ebx, 0x22
		mov ecx, dword ptr [esi + 0x20]
		inc ecx
		push ecx
		sub esp, 8
		// X = [proj+0x34] - qword[0x679338]
		// ★ MSVC 内联汇编 x87 不接受 [绝对地址] 操作数（C2415），先 mov 到 edx 再 [edx]
		fld dword ptr [esi + 0x34]
		mov edx, 0x679338
		fsub qword ptr [edx]
		fstp dword ptr [esp + 4]
		// Y = [proj+0x30] + qword[0x67A288]
		fld dword ptr [esi + 0x30]
		mov edx, 0x67A288
		fadd qword ptr [edx]
		fstp dword ptr [esp]
		mov edx, 0x453C30
		call edx                // eax = 特效对象（0x453C30 内部会改 esi，但已用完）
		// 字段初始化（原版 0x46E298-0x46E2B9）
		mov edi, eax
		mov edx, 0x67952C
		fld dword ptr [edx]
		fstp dword ptr [edi + 4]
		mov edx, 0x679638
		fld dword ptr [edx]
		fstp dword ptr [edi + 8]
		mov edx, 0x679928
		fld dword ptr [edx]
		fstp dword ptr [edi + 0x24]
		mov edx, 0x664A5C
		fld dword ptr [edx]
		fstp dword ptr [edi + 0x34]
	done:
	}
}

// 子弹命中僵尸事件：杨桃弹射 / 火炬过火自定义伤害 / 击退 / 冻结 / 海蘑菇剧毒 都在这里，
// 同样是高危回调（遍历全部僵尸做溅射、std::map 增删）。套 __try，异常落盘后返回 0。
static DWORD onProjectileHitZombieInner(DWORD projectileAddress, DWORD zombieAddress);

DWORD onProjectileHitZombie(DWORD projectileAddress, DWORD zombieAddress)
{
	CRASH_STEP("onProjectileHitZombie:enter");
	__try
	{
		return onProjectileHitZombieInner(projectileAddress, zombieAddress);
	}
	__except (CrashSwallowFilter(GetExceptionInformation()))
	{
		return 0;
	}
}

static DWORD onProjectileHitZombieInner(DWORD projectileAddress, DWORD zombieAddress)
{
	// 子弹命中：手动写 zombie+0x148，游戏不维护子弹来源到此字段
	auto it = g_projectileShooterMap.find(projectileAddress);
	if (it != g_projectileShooterMap.end())
	{
		MemSafeWrite<int>(zombieAddress + 0x148, it->second);
	}

	// ===== 杨桃弹射机制 =====
	auto sfIt = g_starfruitState.find((int)projectileAddress);
	if (sfIt != g_starfruitState.end())
	{
		StarfruitState& s = sfIt->second;
		// 防同一子弹二次命中同一僵尸（用户明确关切点）
		if (s.hitZombies.find((int)zombieAddress) != s.hitZombies.end())
			return 0; // 已命中过该僵尸，忽略（继续飞行）
		s.hitZombies.insert((int)zombieAddress);

		PVZ::Projectile starProj(projectileAddress);
		// 兜底归类：齐射尾 hook 未安装/未触发时（命中时速度必已设置）
		if (s.dir == SD_NONE)
			s.dir = StarClassifyDir(starProj.XSpeed, starProj.YSpeed);

		// 命中动画：在子弹命中位置播放一次杨桃（星星）命中特效
		Creator::CreateEffect(EffectType::STAR, starProj.X, starProj.Y);

		PVZ::Zombie z(zombieAddress);
		if (!z.NotExist)
			z.Hit(STARFRUIT_DAMAGE, PVZ::DAMAGEF_NONE);

		// 弹射判定（60°方向仅弹1次；45°方向 3阶1次/4,5阶2次）
		int dirMax = StarIs60Dir(s.dir) ? 1 : s.maxBounces;
		if (s.bounceIndex < dirMax)
		{
			StarDir next = STAR_NEXT_DIR[s.dir];
			// 向正前飞行的子弹（原"向后"子弹反弹后）：随机向右下45°或右上45°弹射，
			// 使其与其他子弹保持一致（3阶1次/4,5阶2次），而不是弹一次就消失
			if (s.dir == SD_FWD && next == SD_NONE)
				next = (rand() % 2 == 0) ? SD_DR45 : SD_UR45;
			if (next != SD_NONE)
			{
				s.dir = next;
				s.bounceIndex++;
				float sp = (g_starfruitSpeed > 0.1f) ? g_starfruitSpeed : 3.33f;
				starProj.XSpeed = STAR_DIR_VEC[next][0] * sp;
				starProj.YSpeed = STAR_DIR_VEC[next][1] * sp;
				return 0; // 保留子弹（穿透），继续飞行
			}
		}
		// 无可弹射：消耗子弹（手动移除，返回0防止游戏默认伤害二次结算）
		if (!starProj.NotExist)
			starProj.Remove();
		return 0;
	}

	// ===== 火炬树桩过火子弹 自定义伤害处理 =====
	// 游戏原生 FirePea 伤害=40+溅射+defrost，我们拦截并用自定义伤害
	auto fireStateIt = g_projectileFireStates.find(projectileAddress);
	if (fireStateIt != g_projectileFireStates.end())
	{
		auto& fs = fireStateIt->second;
		PVZ::Zombie hitZombie(zombieAddress);
		if (!hitZombie.NotExist)
		{
			// --- 冰火豆：记录延迟减速（先于直伤，确保减速在defrost后生效）---
			auto iceFireIt = g_repeaterIceFireProjectiles.find(projectileAddress);
			if (iceFireIt != g_repeaterIceFireProjectiles.end())
			{
				if (hitZombie.FrozenCountdown > 0)
					hitZombie.FrozenCountdown = 0;
				g_pendingIceFireDecelerates[zombieAddress] = 1000; // 10s
			}

			// --- 5阶：不消除减速/冻结，0-4阶正常消冰 ---
			// Hit() 可能内部修改 DecelerateCountdown/FrozenCountdown，先保存
			int savedDecel = hitZombie.DecelerateCountdown;
			int savedFrozen = hitZombie.FrozenCountdown;

			// 直接伤害
			hitZombie.Hit(fs.damage, PVZ::DAMAGEF_NONE);

			if (!hitZombie.NotExist)
			{
				if (fs.noDefrost)
				{
					// 5阶：恢复减速/冻结
					if (savedDecel > 0) hitZombie.DecelerateCountdown = savedDecel;
					if (savedFrozen > 0) hitZombie.FrozenCountdown = savedFrozen;
				}
				else
				{
					// 0-4阶：正常消除减速/冻结（原版火豌豆行为）
					hitZombie.DecelerateCountdown = 0;
					hitZombie.FrozenCountdown = 0;
				}
			}

			// --- 溅射伤害（原版公式：直伤/范围内僵尸数，上限0.325×直伤，向上取整）---
			int boardAddr = MemSafeRead<int>(PVZ_BASE + 0x768);
			if (boardAddr)
			{
				PVZ::Board board(boardAddr);
				auto allZombies = board.GetAllZombies();
				float hitX = hitZombie.X;
				float hitY = hitZombie.Y;
				int hitRow = (int)hitZombie.Row;
				const float SPLASH_RADIUS = 90.0f;

				// 统计溅射范围内僵尸数（不含直接命中的僵尸）
				std::vector<PVZ::Zombie> splashTargets;
				for (auto& z : allZombies)
				{
					if (z.GetBaseAddress() == zombieAddress) continue;
					if (z.NotExist) continue;
					// ★ 溅射只命中"地面/水面"僵尸（2026-09-24 BUG修复）：
					//   旧写法 DRF_ALL 含 FLYING/SUBMERGED/UNDERGROUND，导致溅射
					//   打到空中气球、未冒头潜水、未出土矿工。DRF_GROUND 排除
					//   BALLOON_FLYING/FALLING、SNORKEL_SWIM、DIGGER_DIG/DRILL/
					//   LOST_DIG/LANDING；已出土矿工(DIZZY/WALK)与冒头吃植物的
					//   潜水(Eating→非submerged)仍正常命中。魅惑排除行为不变。
					if (!z.EffectedBy(PVZ::DRF_GROUND)) continue;
					// ★ 溅射只溅本行（2026-09-26 BUG修复）：原 90px 二维半径纵向
					//   覆盖到邻行（行距约 100px），火豌豆/炎豌豆/冰火豆溅射会打到
					//   邻行僵尸。改为先比行号再算距离；同行僵尸 Y 一致，
					//   二维距离公式退化为 X 距离，保留不影响结果。
					if ((int)z.Row != hitRow) continue;
					float dx = z.X - hitX;
					float dy = z.Y - hitY;
					if (dx * dx + dy * dy <= SPLASH_RADIUS * SPLASH_RADIUS)
						splashTargets.push_back(z);
				}

				int numInRange = (int)splashTargets.size() + 1; // +1 包含直接命中的
				int splashCap = (int)ceil(fs.damage * 0.325f);
				int splashDmg = (int)ceil((float)fs.damage / numInRange);
				if (splashDmg > splashCap) splashDmg = splashCap;

				for (auto& z : splashTargets)
				{
					if (!z.NotExist)
					{
						// 溅射同样按 noDefrost 处理：0-4阶消除减速/冻结（原版火豌豆溅射行为），5阶保留
						int sd = z.DecelerateCountdown;
						int sf = z.FrozenCountdown;
						z.Hit(splashDmg, PVZ::DAMAGEF_NONE);
						if (!z.NotExist)
						{
							if (fs.noDefrost)
							{
								if (sd > 0) z.DecelerateCountdown = sd;
								if (sf > 0) z.FrozenCountdown = sf;
							}
							else
							{
								z.DecelerateCountdown = 0;
								z.FrozenCountdown = 0;
							}
						}
					}
				}
			}
		}

		// 移除过火状态，防止重复处理
		g_projectileFireStates.erase(fireStateIt);
		// ★ 命中粒子：本分支子弹均为火豌豆(Type6)——原版火球命中**不播豌豆爆裂**。
		//   0x25 ZOMBIE_GOT_PEA_SHOT 是普通豌豆特有（0x46D027 lea eax,[esi+0x24] 硬编码，
		//   仅 ecx==0xD 快速路径播）。冰豌豆过0阶火降级普豌豆(0)不插 fireStates → 走原版
		//   原生路径，原生已播 0x25，无需本分支处理。
		//   0x4B/0x4C（ZOMBIE_BOSS_SHOOTED_FIREBALL/LOT_OF_FIRE）是僵王动画，勿用。
		// ★ 火球火焰特效（2026-09-01 复刻原版 0x46E25F 段）：Remove 前播
		//   0x453C30(type 0x22) Reanim 火焰——"火豆打在僵尸上的火焰特效"，一次性视觉。
		//   曾误调 0x532B40（以为点燃）→ 不燃烧且闪白变短（0x52xxxx 解密区假代码解读），勿再调用；
		//   自研染色/DoT 已撤销（原版无持续伤害）。
		FireBallHitEffect(projectileAddress, zombieAddress);
		// 手动移除子弹：返回0会让调用者(0x46D058)认为"未命中"，跳过原生 0x46E000
		// （否则原生 FirePea 伤害40+溅射+defrost 会二次叠加）。不移除子弹的话它会
		// 继续飞行并对后续僵尸造成原生 FirePea 伤害（双重伤害），故必须 Remove。
		// Remove() 调 0x46EB20 → 触发 onProjectileRemove 清理本帧残留标记。
		PVZ::Projectile hitProj(projectileAddress);
		if (!hitProj.NotExist)
			hitProj.Remove();
		// 返回0阻止游戏应用默认FirePea伤害（40+溅射+defrost）
		return 0;
	}

	// ===== 击退效果 =====
	auto kbIt = g_knockbackProjectiles.find(projectileAddress);
	if (kbIt != g_knockbackProjectiles.end())
	{
		PVZ::Zombie zombie(zombieAddress);
		// Pow 特效坐标：命中时僵尸位置（必须在击退移动 X 之前取）
		if (g_kbPowFxQCount < 8)
		{
			g_kbPowFxQ[g_kbPowFxQCount][0] = zombie.X + KB_POW_FX_DX;
			g_kbPowFxQ[g_kbPowFxQCount][1] = zombie.Y + KB_POW_FX_DY;
			g_kbPowFxQCount++;
		}
		float newX = zombie.X + (float)g_knockbackDistance;
		if (newX < 0.0f) newX = 0.0f;
		zombie.X = newX;
		g_knockbackProjectiles.erase(kbIt);
		// 命中即销毁弹体：此处清贴图标记（移除事件的清理因集合已空不会再触发）
		MemSafeWrite<int>(projectileAddress + 0x78, 0);
	}

	// ===== 寒冰射手 冻结效果（三/四阶）=====
	auto freezeIt = g_snowPeaFreezeProjectiles.find(projectileAddress);
	if (freezeIt != g_snowPeaFreezeProjectiles.end())
	{
		PVZ::Zombie zombie(zombieAddress);
		if (!zombie.NotExist)
			zombie.Froze(200); // 冻结2s（200厘秒）
		g_snowPeaFreezeProjectiles.erase(freezeIt);
	}

	// ===== 寒冰射手 冰锥效果（五阶）=====
	auto icicleIt = g_snowPeaIcicleProjectiles.find(projectileAddress);
	if (icicleIt != g_snowPeaIcicleProjectiles.end())
	{
		auto& hitSet = g_icicleHitZombies[projectileAddress];
		if (hitSet.find(zombieAddress) == hitSet.end())
		{
			hitSet.insert(zombieAddress);
			PVZ::Zombie zombie(zombieAddress);
			if (!zombie.NotExist)
			{
				// ★ 先读减速状态——HitBody 执行游戏 ASM 会覆盖 DecelerateCountdown
				bool wasSlowed = (zombie.DecelerateCountdown > 0);
				// 伤害40，无视二类防具（铁门、报纸等）
				zombie.HitBody(40, PVZ::DAMAGEF_BYPASSES_SHIELD);
				// 已被减速 → 冻结2s（解冻后减速8s）；未减速 → 减速8s
				if (!zombie.NotExist)
				{
					if (wasSlowed)
					{
						zombie.Froze(200);
						// Froze() 内部会恢复 DecelerateCountdown 原值，
						// 手动覆写确保解冻后仍减速 8s
						zombie.DecelerateCountdown = 800;
					}
					else
						zombie.Decelerate(800);
				}
			}
		}
		// 返回0防止游戏移除冰锥子弹（实现穿透效果）
		return 0;
	}

	// ===== 双发射手 冰火豌豆效果 =====
	// 火豌豆伤害+溅射+defrost由OnFire()/游戏自身处理。
	// 这里只记录僵尸地址，减速延迟到下一帧onGameObjectsUpdate执行，
	// 确保游戏原生火豌豆defrost先完成，然后再上减速。
	auto iceFireIt = g_repeaterIceFireProjectiles.find(projectileAddress);
	if (iceFireIt != g_repeaterIceFireProjectiles.end())
	{
		PVZ::Zombie zombie(zombieAddress);
		if (!zombie.NotExist)
		{
			// 如果僵尸处于冻结状态，先消除冻结
			if (zombie.FrozenCountdown > 0)
				zombie.FrozenCountdown = 0;
			// 记录延迟减速（下一帧执行）
			g_pendingIceFireDecelerates[zombieAddress] = 1000; // 10s
		}
	}

	// ===== 冰西瓜（WinterMelon, SeedType=44）等阶机制 =====
	// ① 小冰瓜（5阶大招散射弹，[proj+0x8C]==200 标记）：拦截原版结算 →
	//    自定义 10 伤害（走 Hit 正常流程，先护甲）+ 减速；返回 0 + 手动 Remove
	//    （同杨桃/冰锥模式：返回 0 防原版二次伤害，Remove 触发清理事件）
	// ② 普通冰瓜：原版结算伤害/减速；4阶起命中时按概率追加冻结 4 秒（Froze 会清减速，
	//    故保留原版减速先跑完——冻结在命中后立即施加，解冻后不再补减速，符合"冻结 4 秒"语义）
	{
		int iceMark = MemSafeRead<int>(projectileAddress + 0x8C);
		if (iceMark == ICE_MELON_SMALL_MARK)
		{
			// ★★ 需求定案：小冰瓜撞到谁就结算谁（无目标锁定）。
			g_iceDiagSmallSeq++;   // POD 诊断：小冰瓜命中计数（事件帧只写内存，轮询帧落盘）
			g_iceDiagSmallHitProj = projectileAddress;
			g_iceDiagSmallHitZ = zombieAddress;
			PVZ::Zombie zz(zombieAddress);
			if (!zz.NotExist)
			{
				// 有来源伤害：先写伤害来源（击杀经验归冰西瓜），再走正常 Hit（护甲优先）
				auto shIt = g_projectileShooterMap.find(projectileAddress);
				if (shIt != g_projectileShooterMap.end() && shIt->second)
				{
					DWORD src = (DWORD)shIt->second;
					if (!MemSafeRead<BYTE>(src + 0x141))
						MemSafeWrite<int>(zombieAddress + 0x148, (int)src);
				}
				zz.Hit(ICE_MELON_SMALL_DAMAGE, PVZ::DAMAGEF_NONE);
				if (!zz.NotExist)
					zz.Decelerate(1000);   // 小冰瓜带减速（10 秒，原版冰瓜同款量级）
			}
			// ★ 命中粒子特效（原版"冰瓜：破裂" 0x01，不缩放）：
			//   本分支走自定义结算（Hit + Remove + return 0）绕过了原版命中流程，
			//   原版粒子自然不会播 —— 登记坐标到 POD 队列，下一帧安全上下文 spawn。
			//   ★ 绝不能在本事件帧直接 spawn（粒子生成是重活，事件帧内调用会崩）。
			if (g_iceMelonFxQCount < 16)
			{
				g_iceMelonFxQ[g_iceMelonFxQCount].x = MemSafeRead<float>(projectileAddress + 0x30); // 命中点 X
				g_iceMelonFxQ[g_iceMelonFxQCount].y = MemSafeRead<float>(projectileAddress + 0x34); // 命中点 Y
				g_iceMelonFxQCount++;
			}
			// 移除子弹（防原版再结算一次伤害）；返回 0 阻止游戏默认流程再次伤害
			PVZ::Projectile proj(projectileAddress);
			if (!proj.NotExist)
				proj.Remove();
			return 0;
		}

		// 普通冰瓜 4阶命中冻结：仅当发射者是 4 阶及以上的冰西瓜
		// ★★ 守卫改为 "iceMark != 200"（2026-09-11 定案）：不能依赖 "== 0"——
		//   [proj+0x8C] 是模组自定义通道，游戏创建弹体不清零（PVZ.h 无该字段定义），
		//   普通冰瓜的 mark 可能是任意堆残留/槽位复用残留的垃圾值 → "== 0" 守卫永不成立
		//   → 冻结分支 0 执行（日志实锤：DIAG hit 0 条 / DIAG small 正常）。
		//   小冰瓜由散射代码显式写 200，判"非 200"即可靠区分。
		// ★★ 铁律（2026-09-11 日志实锤）：命中事件帧内严禁 IceLog/fopen 等 CRT！
		//   诊断 POD 化：事件帧只写普通变量，轮询帧（IceMelonFreezeFrame）检测序列号
		//   变化后统一 IceLog 落盘。
		if (iceMark != ICE_MELON_SMALL_MARK)
		{
			auto shIt = g_projectileShooterMap.find(projectileAddress);
			// ---- POD 诊断：进入分支即记录（原始 mark + 弹型 + 来源映射），轮询帧落盘。
			//   仅记录瓜类弹（Type 3=Melon / 5=WinterMelon）防全弹种刷屏。
			int diagPtype = MemSafeRead<int>(projectileAddress + 0x5C);
			if (diagPtype == 5 || diagPtype == 3)
			{
				g_iceDiagProj = projectileAddress;
				g_iceDiagZombie = zombieAddress;
				g_iceDiagMark = iceMark;
				g_iceDiagPtype = diagPtype;
				g_iceDiagMapSrc = (shIt != g_projectileShooterMap.end() && shIt->second)
					? (DWORD)shIt->second : 0;
				g_iceDiagStier = -999;   // 哨兵：未通过来源校验（没走到等阶判定那步）
				g_iceDiagRoll = -1;
				g_iceDiagFroze = 0;
				g_iceDiagHitSeq++;
			}
			if (shIt != g_projectileShooterMap.end() && shIt->second)
			{
				DWORD src = (DWORD)shIt->second;
				if (MemSafeRead<int>(src + 0x24) == (int)SeedType::WinterMelon
					&& !MemSafeRead<BYTE>(src + 0x141))
				{
					int sexp = 0;
					auto eIt = g_plantExperience.find(src);
					if (eIt != g_plantExperience.end()) sexp = eIt->second;
					int stier = GetPlantTier((int)SeedType::WinterMelon, sexp);
					if (diagPtype == 5 || diagPtype == 3)
						g_iceDiagStier = stier;
					if (stier >= 4 && g_iceMelonFreezeProbability > 0)
					{
						int roll = rand() % 100;
						if (diagPtype == 5 || diagPtype == 3)
							g_iceDiagRoll = roll;
						if (roll < g_iceMelonFreezeProbability)
						{
							// ★ 照抄寒冰射手 3/4 阶写法：就地在命中事件帧调 Froze（该路径实测有效）。
							//   注：原生 FROZE 用随机值(300/300+rand/400+rand)覆盖 FrozenCountdown，
							//   传入 cs 不决定时长；"冻结 4 秒"≈原生量级，直接用其原生行为。
							PVZ::Zombie zz(zombieAddress);
							if (!zz.NotExist)
							{
								zz.Froze(ICE_MELON_FREEZE_CS);
								// 解冻后 10 秒减速：登记再断言窗口（冻结期内每帧补 +0xAC）
								IceMelonAddSlowWindow(zombieAddress);
								if (diagPtype == 5 || diagPtype == 3)
									g_iceDiagFroze = 1;
							}
						}
					}
				}
			}
		}
	}

	// ===== 海蘑菇（SeaShroom, SeedType=24）剧毒 =====
	// 子弹来源植物是海蘑菇时：按等阶附加剧毒层数（0阶1层 / 1阶2层 / 3阶3层）。
	// 5阶且层数≥阈值 → 触发"毒爆"：15倍层数直伤 + 3×3范围僵尸附加10层毒。
	// 直伤 10 为原版值，由游戏原生 Puff 子弹伤害结算，此处不干预（返回 zombieAddress 继续）。
	// ★ 毒爆伤害/溅射附毒都走 Hit/附毒路径写 zombie+0x148=海蘑菇 → 毒死的僵尸经验归海蘑菇。
	{
		auto sIt = g_projectileShooterMap.find(projectileAddress);
		if (sIt != g_projectileShooterMap.end())
		{
			DWORD plantAddr = (DWORD)sIt->second;
			if (plantAddr && MemSafeRead<int>(plantAddr + 0x24) == (int)SeedType::Seashroom)
			{
				auto expIt = g_plantExperience.find(plantAddr);
				int tier = (expIt != g_plantExperience.end())
					? GetPlantTier((int)SeedType::Seashroom, expIt->second) : 0;

				int cur = GetPoisonStacks(zombieAddress);
				if (tier >= 5 && cur >= g_seaBurstThreshold)
				{
					// 毒爆：本次命中不再附加普通层数（爆炸即全部效果）
					int boardAddr = MemSafeRead<int>(PVZ_BASE + 0x768);
					SeaShroomBurst(zombieAddress, plantAddr, boardAddr);
				}
				else
				{
					int stack = (tier >= 3) ? g_seaStackT3 : (tier >= 1) ? g_seaStackT1 : g_seaStackT0;
					AddPoisonStacks(zombieAddress, stack, plantAddr);
				}
			}
		}
	}

	return zombieAddress;
}

// ==================== 西瓜大炮（5阶西瓜投手）落地溅射 ====================
// 音效播放（S4/S6 同款调用约定，原版反汇编 0x45FA9D 铁证：eax=LawnApp, esi=音效ID，无栈参）
static void MelonPlaySound(int soundId)
{
	__asm
	{
		pushad
		mov eax, 0x6A9EC0
		mov eax, dword ptr [eax]
		test eax, eax
		jz melonSndDone
		mov esi, soundId
		mov ebx, 0x453630
		call ebx
	melonSndDone:
		popad
	}
}

// 落地特效：单层樱桃爆炸（0x04）+ 贴图替换为西瓜泼溅大图（不缩放——用户改需求：
// 特效不变大，改为飞行中的大炮弹贴图变大，见 ProjectileMelonBig.png 弹体贴图替换）。
// y 锚定弹体影子 ShadowY(+0x4C)（=弹体正下方地面）上方 25px。
// __try 包裹（无 C++ 对象，不触发 C2712）；异常只跳过特效，fxErr++ 留痕。
static void MelonCannonFX(float fx, float groundY)
{
	__try
	{
		// IMAGE_MELONPULT_PARTICLES（西瓜泼溅贴图，exe 资源定义表扫出 0x6A73BC = 图指针全局）
		DWORD melonImg = MemSafeRead<DWORD>(0x6A73BC);
		DWORD psys = SeaBurstSpawnParticle(fx - 10.0f, groundY - 25.0f, 0x04);
		if (psys && melonImg)
			SeaBurstOverrideImage(psys, melonImg);
		MelonPlaySound(55);   // CherryExplode（S4 落地音效）
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_melFxErr++;
	}
}

// 落点群伤（本行 ±110px 无衰减 / 邻行 ±40px 无衰减；S4特性表：前后 1.375 格 / 0.5 格，1 格=80px）。
// ★ boardAddr 必须是真正的 Board 指针（LawnApp+0x768），旧版误传 LawnApp 导致 GetAllZombies
//   读不到僵尸 = "大炮零伤害"根因（长期笔记铁律"+0 机制必失效"又一实例）。
// ★ 有来源伤害：命中前写僵尸伤害来源字段（z+0x148）= 发射西瓜地址（金盏花同款先例），
//   击杀经验归西瓜（经验分配机制依赖来源字段）。来源植物已死/被铲则不写（无来源）。
// 伤害走 Zombie::Hit 正常流程（护甲优先吸收，与原版溅射一致）；魅惑僵尸不打（S4 同款）。
// 注意：本函数含 std::vector，不得与 __try 同函数（C2712）。
static void MelonCannonDamage(float mx, int prow, DWORD boardAddr, DWORD srcPlant)
{
	if (!boardAddr || prow < 0 || prow > 5)
		return;
	bool srcAlive = srcPlant && !MemSafeRead<BYTE>(srcPlant + 0x141);
	PVZ::Board board(boardAddr);
	auto zombies = board.GetAllZombies();
	for (auto& z : zombies)
	{
		if (z.NotExist) continue;
		if (z.Hypnotized) continue;
		// ★ 只排除未出土矿工（用户规格 2026-09-24：能打潜水与气球，不能打矿工）。
		//   DIGGER_DIG=地下挖行、DRILL/LOST_DIG=地下钻行、LANDING=出土落地中；
		//   已出土矿工(DIZZY/WALK/IDLE)与普通地面、潜水、气球(飞天/下落)均正常命中。
		//   不用 EffectedBy 组合——其 OFF_GROUND 会连带排除 BALLOON_FALLING/墓碑出土，
		//   与"能打气球"的规格冲突，故手写矿工四态判断。
		ZombieState::ZombieState zst = z.State;
		if (zst == ZombieState::DIGGER_DIG || zst == ZombieState::DIGGER_DRILL
			|| zst == ZombieState::DIGGER_LOST_DIG || zst == ZombieState::DIGGER_LANDING)
			continue;
		int dr = (int)z.Row - prow;
		if (dr < -1 || dr > 1) continue;
		float zx = z.X;
		if (dr == 0)
		{
			if (mx >= zx - 110.0f && mx <= zx + 110.0f)
			{
				if (srcAlive)
					MemSafeWrite<int>(z.GetBaseAddress() + 0x148, (int)srcPlant);
				z.Hit(g_melonCannonDamage, PVZ::DAMAGEF_NONE);
				MelonPlaySound(62);   // MelonHit（S4 同款命中音效）
			}
		}
		else
		{
			if (mx >= zx - 40.0f && mx <= zx + 40.0f)
			{
				if (srcAlive)
					MemSafeWrite<int>(z.GetBaseAddress() + 0x148, (int)srcPlant);
				z.Hit(MELON_CANNON_SIDE_DAMAGE, PVZ::DAMAGEF_NONE);
				MelonPlaySound(62);
			}
		}
	}
}

// 每帧维护（onGameObjectsUpdate 调用，传入 boardAddress）。两段：
// ② 落地溅射结算：onProjectileRemove 只记录坐标+来源（此刻弹体字段仍有效），下一帧统一结算——
//    不在 Die 事件栈内做粒子/音效/伤害（毒爆 FX+Hit 全在轮询帧做，是本项目已验证的安全模式）
// ③ 大炮弹逐帧维护：
//    - ★每帧清 DamageAbility(+0x74)=0（S4"子弹综算"同款：游戏创建子弹时会写该字段，
//      只在发射时清一次会被覆盖 → 弹体照样砸僵尸头，这是上一版"仍砸头+崩溃"的根因）
//    - ★★ 主动杀弹已整体禁用（g_melonTickKillEnable=false）：四轮实测证明兜底判据会误杀弹体
//      （无宽限→原地炸；带 ex>20 宽限→上升途中半空炸；第五轮排除法禁用后弹道全部正常——定案）。
//      tag=0 后弹体飞过头顶由【原版自己的落地死亡】结算（0x46D67A→0x46D826→0x46E000→Die），
//      tick 只做被动维护（清标签/溅射结算），绝不主动杀弹。
//    - 唯一兜底：存在超 600 帧（10 秒，正常飞行 <2 秒）→ 强制 Die，防"永不落地"极端异常
static bool g_melonTickKillEnable = false;
static void MelonCannonTick(DWORD boardAddress)
{
	// 落地溅射结算（延迟一帧；boardAddress = 真正的 Board，直接来自 onGameObjectsUpdate）
	if (g_melonPendingSplash.active)
	{
		g_melonPendingSplash.active = 0;
		MelonCannonFX(g_melonPendingSplash.x, g_melonPendingSplash.groundY);
		MelonCannonDamage(g_melonPendingSplash.x, g_melonPendingSplash.row, boardAddress,
			g_melonPendingSplash.plant);
		g_melonPendingSplash.plant = 0;
	}
	// 大炮弹维护
	for (int i = 0; i < 8; i++)
	{
		MelonCannonSlot* s = &g_melonCannonSlots[i];
		if (!s->active) continue;
		// 槽位校验：弹体已消失 / Id 不符（地址被复用）→ 静默摘槽
		if (MemSafeRead<byte>(s->proj + 0x50)
			|| MemSafeRead<int>(s->proj + 0x90) != s->id)
		{
			s->active = 0;
			continue;
		}
		// ★S4 同款：每帧清索敌标签 → 弹体不撞僵尸、飞过头顶
		MemSafeWrite<int>(s->proj + 0x74, 0);
		int ex = MemSafeRead<int>(s->proj + 0x60);           // ExistedTime
		// ★★ 主动杀弹已禁用（排除法定案）——弹体死亡完全交给原版落地死亡。
		// 以下代码保留但默认不执行，g_melonTickKillEnable=true 可重新启用以便对照测试
		if (g_melonTickKillEnable)
		{
			float h  = MemSafeRead<float>(s->proj + 0x38);   // Height
			float hs = MemSafeRead<float>(s->proj + 0x44);   // HeightSpeed
			float visY = MemSafeRead<float>(s->proj + 0x34) + h;
			float dy   = visY - s->lastVisY;
			if (dy < 0.5f && dy > -0.5f)
				s->stall++;
			else
				s->stall = 0;
			s->lastVisY = visY;
			if (ex > 20 && ((hs < 0.0f && h <= 5.0f) || s->stall >= 20))
			{
				DWORD p = s->proj;   // 槽保持 active，Die 事件里摘槽
				__asm
				{
					pushad
					mov eax, p
					mov ebx, 0x46EB20   ; 原版 Projectile::Die（eax=弹体，S4 脚本同款调用）
					call ebx
					popad
				}
			}
		}
		// 最终兜底：存在超 600 帧（10 秒，正常飞行 <2 秒必被原版落地死亡结算）→ 强制 Die。
		// 无任何弹道判据，只在"弹体真的永远不死"的极端异常时触发，不会误伤正常弹道
		else if (ex > 600)
		{
			DWORD p = s->proj;
			__asm
			{
				pushad
				mov eax, p
				mov ebx, 0x46EB20
				call ebx
				popad
			}
		}
	}
}

int onProjectileRemove(DWORD projectileAddress)
{
	// 西瓜大炮弹死亡（原版落地死亡 / tick 兜底 Die / 飞出屏幕）：摘槽 + 记录待结算坐标
	// （弹体字段此刻仍有效；特效/音效/伤害延迟到下一帧 tick 结算，不在 Die 事件栈内做）
	MelonCannonSlot* mcSlot = MelonCannonFind(projectileAddress);
	if (mcSlot)
	{
		mcSlot->active = 0;
		g_melonPendingSplash.active  = 1;
		g_melonPendingSplash.x       = MemSafeRead<float>(projectileAddress + 0x30);  // X
		g_melonPendingSplash.groundY = MemSafeRead<float>(projectileAddress + 0x4C);  // ShadowY（正下方地面）
		g_melonPendingSplash.row     = MemSafeRead<int>(projectileAddress + 0x1C);    // Row
		g_melonPendingSplash.plant   = mcSlot->plant;   // 发射者（击杀经验归属）
	}

	// ===== 卷心菜投手 T5 弹射：命中死亡的弹体登记物理反弹（下一帧 tick 结算）=====
	// 事件帧只做 POD 写入 + map find/erase（先例充分），不做发射/遍历等重活
	{
		// 已弹射过的弹体（弹射补投的新弹）：消费标记，直接放行（防无限连锁）
		auto nbIt = g_cabbageNoBounce.find(projectileAddress);
		if (nbIt != g_cabbageNoBounce.end())
		{
			g_cabbageNoBounce.erase(nbIt);
		}
		// 卷心菜弹体（ProjectileType::Cabbage=2，[proj+0x5C]）+ 发射者是活着的 5 阶卷心菜投手
		else if (MemSafeRead<int>(projectileAddress + 0x5C) == (int)ProjectileType::Cabbage
			&& g_cabbageBounceCount < 16)
		{
			auto shIt = g_projectileShooterMap.find(projectileAddress);
			if (shIt != g_projectileShooterMap.end())
			{
				DWORD shooterPlant = shIt->second;
				bool plantAlive = shooterPlant
					&& !MemSafeRead<BYTE>(shooterPlant + 0x141)
					&& MemSafeRead<int>(shooterPlant + 0x24) == (int)SeedType::Cabbagepult;
				int shooterTier = 0;
				if (plantAlive)
				{
					int sexp = 0;
					auto sexpIt = g_plantExperience.find(shooterPlant);
					if (sexpIt != g_plantExperience.end()) sexp = sexpIt->second;
					shooterTier = GetPlantTier((int)SeedType::Cabbagepult, sexp);
				}
				if (plantAlive && shooterTier >= 5)
				{
					CabbageBounceReq& rq = g_cabbageBounceQ[g_cabbageBounceCount++];
					rq.plant = shooterPlant;
					rq.x = MemSafeRead<float>(projectileAddress + 0x30);  // 命中点 X
					rq.y = MemSafeRead<float>(projectileAddress + 0x4C);  // ShadowY（命中点正下方地面 Y，弹射起跳基准）
					rq.row = MemSafeRead<int>(projectileAddress + 0x1C);  // Row
					rq.vel = MemSafeRead<float>(projectileAddress + 0x44); // 命中瞬间垂直速度（正=下落）
					rq.xs  = MemSafeRead<float>(projectileAddress + 0x3C); // 命中瞬间水平速度
				}
			}
		}
	}

	auto it = g_projectileShooterMap.find(projectileAddress);
	if (it != g_projectileShooterMap.end())
	{
		g_projectileShooterMap.erase(it);
	}

	// 清理杨桃弹射状态
	auto sfIt = g_starfruitState.find((int)projectileAddress);
	if (sfIt != g_starfruitState.end())
		g_starfruitState.erase(sfIt);

	// 清理击退标记
	auto kbIt = g_knockbackProjectiles.find(projectileAddress);
	if (kbIt != g_knockbackProjectiles.end())
	{
		g_knockbackProjectiles.erase(kbIt);
		MemSafeWrite<int>(projectileAddress + 0x78, 0); // 清贴图标记防内存池复用
	}

	// 清理小冰瓜标记（命中后已 Remove，此处兜底复位字段防内存池复用污染）：
	// 只处理带小冰瓜标记的弹体，绝不无条件清零 [proj+0x8C]——那是豌豆染色标记通道
	if (MemSafeRead<int>(projectileAddress + 0x8C) == ICE_MELON_SMALL_MARK)
	{
		MemSafeWrite<int>(projectileAddress + 0x8C, 0);
		MemSafeWrite<int>(projectileAddress + 0x78, 0);
	}

	// 清理寒冰射手相关标记
	auto freezeIt = g_snowPeaFreezeProjectiles.find(projectileAddress);
	if (freezeIt != g_snowPeaFreezeProjectiles.end())
	{
		g_snowPeaFreezeProjectiles.erase(freezeIt);
		MemSafeWrite<int>(projectileAddress + 0x78, 0); // 清贴图标记防内存池复用
	}

	auto icicleIt = g_snowPeaIcicleProjectiles.find(projectileAddress);
	if (icicleIt != g_snowPeaIcicleProjectiles.end())
	{
		g_snowPeaIcicleProjectiles.erase(icicleIt);
		g_icicleHitZombies.erase(projectileAddress);
		g_speedBoostedIcicles.erase(projectileAddress);
		g_iciclePrevX.erase(projectileAddress);
		MemSafeWrite<int>(projectileAddress + 0x78, 0); // 清贴图标记防内存池复用
	}

	// 清理双发射手冰火豌豆标记
	auto repeaterIt = g_repeaterIceFireProjectiles.find(projectileAddress);
	if (repeaterIt != g_repeaterIceFireProjectiles.end())
		g_repeaterIceFireProjectiles.erase(repeaterIt);

	// 清理火炬树桩过火状态
	auto fireStateIt = g_projectileFireStates.find(projectileAddress);
	if (fireStateIt != g_projectileFireStates.end())
		g_projectileFireStates.erase(fireStateIt);

	// 清理裂荚射手方向标记（防内存池复用：标记残留会让复用子弹被误判为裂荚子弹）
	// ★ 标记字段是 +0x80（不是 +0x78，那是原生 lastTorchCol）；连带清 +0x84 初始X
	if (MemSafeRead<int>(projectileAddress + 0x80) == SPLIT_PEA_LEFT ||
		MemSafeRead<int>(projectileAddress + 0x80) == SPLIT_PEA_RIGHT ||
		MemSafeRead<int>(projectileAddress + 0x80) == SPLIT_PEA_LEFT_NB)
	{
		MemSafeWrite<int>(projectileAddress + 0x80, 0);
		MemSafeWrite<float>(projectileAddress + 0x84, 0.0f);
	}

	// 清理三线射手标记（map.erase，事件帧安全——onProjectileRemove 大量 std::map erase 先例）
	// ★ 不再写原生 [proj+0x80]/[0x84]（原版标志字段，写大值会致子弹被原生误移除）
	g_tripleMark.erase(projectileAddress);

	// 清理机枪射手大招弹标记（行号重算名单；事件帧 map.erase 先例同上）
	g_gatlingUltMark.erase(projectileAddress);

	return 0;
}

// ==================== 金盏花（Marigold）形态产出物机制 ====================
// 设计（2026-08-26）：
//   金盏花与保护伞一样需要咖啡豆唤醒才解锁等阶（3阶满阶，plant_tier.ini 38=1500,250,800,1500,1500,1500）。
//   形态由鼠标右键轮换（0白/1蓝/2黄/3绿，受等阶上限约束），切换播放特效46(看星星特效)。
//   形态决定产出物（产出物素材全部取自禅境花园 images 目录）：
//     白(0阶)=肥料包 Fertilizer.png  给植物 +300 经验（同经验包）
//     蓝(1阶)=水壶   WateringCan.png 给植物回 300 血（含 anim_water_area 浇水动画）
//     黄(2阶)=留声机 Phonograph.png  给植物攻速加成一段时间
//     绿(3阶)=杀虫剂 bug_spray.png   对指定格子每秒 50 真伤（HitBody 无视护甲，有来源=金盏花）
//   产出：Hook 原版产金币点 0x45FB1D（call 0x40CB10，金盏花/向日葵/双子/阳光菇共用），
//         类型==38 时改为产产出物并跳过原版金币；其余植物走原版。
//   使用：单击产出物拾起(图标跟随鼠标) → 拖动 → 单击目标植物/格子生效 → 消耗。
// 安全铁律：产出 hook 回调帧内纯 POD 读写（禁 std::map/fopen，崩溃铁律）；
//   轮询/绘制/交互函数全部 __try 包裹（同保护伞/经验包模式）。
// 全局变量/结构体声明在"金盏花配置"段（LoadPlantMechanicsConfig 之前），
// 全部实现函数在本段。

// 正确调用游戏 Reanimation::CreateReanimation @0x453C30（修复框架 Creator 版本参数错位）
// 0x453C30 调用约定（反汇编确认）：栈参数 arg1=X, arg2=Y, arg3=layer（ret 0xC）；
//   eax=LawnApp, ebx=reanim 类型；返回 eax=Reanimation 地址。
// ★ 框架 Creator::CreateReanimation(type,x,y,layer) 把参数压成 (layer,x,y) → X/Y/layer 全错位，
//   实测水壶动画位置不对即此因；本函数按游戏真实约定调用。
static DWORD MgCreateReanim(int reanimType, float x, float y, int layer)
{
	DWORD result = 0;
	__asm {
		mov eax, 0x6A9EC0
		mov eax, dword ptr [eax]    ; eax = LawnApp
		mov ebx, reanimType         ; ebx = reanim 类型（★参数名不能用 type：与 MASM TYPE 保留字冲突 C2400）
		push layer
		sub esp, 8
		fld y
		fstp dword ptr [esp+4]
		fld x
		fstp dword ptr [esp]
		mov edx, 0x453C30
		call edx                    ; ret 0xC 清 12 字节
		mov result, eax
	}
	return result;
}

// 金盏花形态染色：只染花瓣轨道（Marigold_petals 贴图）
// ★ SetImageOverride 替换花瓣轨道图片（0x473490: ecx=reanim, eax=轨道名, [esp]=image, ret 4）；
//   轨道实例 +0x44 = image override（0x4734A6 写入）。染色图在 images\（生成自 reanim\Marigold_petals.png）。
//   白色形态 = 替换回原图（游戏 reanim\Marigold_petals.png）。
static void MgApplyPetalsTint(DWORD plantAddr, int form)
{
	PVZ::Plant p(plantAddr);
	PVZ::Animation anim = p.GetAnimationPart1();
	if (!anim.GetBaseAddress())
		return;
	if (form < 0) form = 0;
	if (form > 3) form = 3;
	DWORD img = (form == 0) ? g_mgImgPetalsOrig
		: (form == 1) ? g_mgImgPetalsBlue
		: (form == 2) ? g_mgImgPetalsYellow : g_mgImgPetalsGreen;
	if (!img)
		return;
	__try
	{
		// ★ 防护：先确认花瓣轨道存在（FindTrackIndex >= 0），否则 SetImageOverride 内部用 -1 索引会越界写
		//   （ReanimSetImageOverride 内部还会再自检一次，双保险）
		if (ReanimTrackIndex(anim.GetBaseAddress(), "Marigold_petals") < 0)
			return;
		ReanimSetImageOverride(anim.GetBaseAddress(), "Marigold_petals", img);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 隐藏 reanim 中名字含 "gold" 的轨道（Kettle 水壶有普通/金两个轨道，只保留普通水壶）
static void MgHideGoldTrack(DWORD reanim)
{
	if (!reanim)
		return;
	__try
	{
		// [reanim+0xC] = trackDefs 数组对象 {数据指针, 数量}；
		// ★ 数据区每 0xC 字节一个 4 字节指针 = 轨道名字符串指针（0x472F30 FindTrackIndex 确认）
		int arr = MemSafeRead<int>(reanim + 0xC);
		if (!arr)
			return;
		int count = MemSafeRead<int>(arr + 4);
		int ptr = MemSafeRead<int>(arr + 0);
		if (!ptr || count <= 0 || count > 64)
			return;
		for (int i = 0; i < count; i++)
		{
			int namePtr = MemSafeRead<int>(ptr + i * 0xC);
			if (namePtr < 0x400000 || namePtr > 0x800000)
				continue;
			char buf[64];
			PVZ::Memory::ReadArray<char>(namePtr, buf, 63);
			buf[63] = 0;
			if (strstr(buf, "gold") || strstr(buf, "Gold") || strstr(buf, "GOLD"))
			{
				PVZ::Animation anim(reanim);
				anim.AssignRenderGroupToTrack(buf, 0xFF);   // 渲染组 -1(0xFF) = 隐藏轨道
			}
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 查找/登记金盏花记录（纯 POD，hook 帧内安全）
static MgPlantRec* MgFindPlantRec(DWORD plant)
{
	for (int i = 0; i < g_mgPlantCount; i++)
		if (g_mgPlants[i].plant == plant)
			return &g_mgPlants[i];
	return 0;
}
static int MgGetForm(DWORD plant)
{
	MgPlantRec* r = MgFindPlantRec(plant);
	return r ? r->form : 0;
}
static void MgSetForm(DWORD plant, int form)
{
	MgPlantRec* r = MgFindPlantRec(plant);
	if (r)
		r->form = form;
	else if (g_mgPlantCount < MG_MAX_PLANTS)
	{
		g_mgPlants[g_mgPlantCount].plant = plant;
		g_mgPlants[g_mgPlantCount].form = form;
		g_mgPlants[g_mgPlantCount].lastTint = -1;
		g_mgPlants[g_mgPlantCount].lastReanim = 0;
		g_mgPlantCount++;
	}
}

static int MgPlayingTime()
{
	int pvzBase = MemSafeRead<int>(0x6A9EC0);
	if (pvzBase < 0x400000) return 0;
	int board = MemSafeRead<int>(pvzBase + 0x768);
	if (!board) return 0;
	return MemSafeRead<int>(board + 0x5568);
}

// 产出：金盏花登记一个产出物。
// ★ 产出时先销毁该株所有未选中的旧物品（旧物品此时已完成渐隐 cd<=25，必须消失并销毁，
//   不能留在数组里——否则游戏把产出倒计时重置后 cd>25，旧物品会"重新出现"）。
//   正在拖拽使用的选中项保留（拖完即用，不受影响）。新物品固定放在槽位 0。
static void MgSpawnItem(DWORD plant, int type)
{
	if (type < 0) type = 0;
	if (type > 3) type = 3;
	// 1) 暂存选中项（若有）
	MgItemRec sel;
	bool hasSel = false;
	for (int i = 0; i < g_mgItemCount; i++)
	{
		if (g_mgSelected == i)
		{
			sel = g_mgItems[i];
			hasSel = true;
			break;
		}
	}
	// 2) 压缩数组：丢弃本株所有未选中旧物品（保留其他株物品与选中项）
	int w = 0;
	for (int i = 0; i < g_mgItemCount; i++)
	{
		if (g_mgItems[i].plant == plant && g_mgSelected != i)
			continue;   // 销毁
		g_mgItems[w++] = g_mgItems[i];
	}
	g_mgItemCount = w;
	g_mgSelected = -1;
	if (hasSel)
	{
		g_mgItems[g_mgItemCount++] = sel;
		g_mgSelected = g_mgItemCount - 1;
	}
	// 3) 添加新物品（★ 记录独立生命周期）
	if (g_mgItemCount >= MG_MAX_ITEMS)
		return;
	// hook 帧内：产金币点 0x45FB1D 触发时，游戏已把产出倒计时重置为新值（0x45FA98 在
	// 产金币之前执行）→ 此时 [plant+0x58] 就是"到下次产出的时长"，正好作为本物品寿命。
	int lifeCs = MemSafeRead<int>(plant + 0x58);
	if (lifeCs <= 0 || lifeCs > 100000)
		lifeCs = 2400;   // 异常兜底（原版约 24 秒）
	g_mgItems[g_mgItemCount].plant = plant;
	g_mgItems[g_mgItemCount].type = type;
	g_mgItems[g_mgItemCount].serial = g_mgItemSerial++;
	g_mgItems[g_mgItemCount].spawnCs = MgPlayingTime();
	g_mgItems[g_mgItemCount].lifeCs = lifeCs;
	g_mgItemCount++;
}

// ★ 物品剩余寿命（厘秒）= 寿命 - 已存在时长。基于物品自身记录，与实时倒计时无关。
//   倒计时归零/玩家拾起取消后依然准确 → 修复"物品该消失却不消失（时有时无）"。
static int MgItemRemainCs(int itemIdx)
{
	if (itemIdx < 0 || itemIdx >= g_mgItemCount)
		return -1;
	int life = g_mgItems[itemIdx].lifeCs;
	if (life <= 0)
		life = 2400;
	return life - (MgPlayingTime() - g_mgItems[itemIdx].spawnCs);
}

// 产出物屏幕中心（含浮动 bob；plant 死亡返回 false；完全淡出后返回 false 不可点）
static bool MgItemCenter(int itemIdx, int* outCx, int* outCy)
{
	if (itemIdx < 0 || itemIdx >= g_mgItemCount)
		return false;
	DWORD plant = g_mgItems[itemIdx].plant;
	if (!plant)
		return false;
	if (MemSafeRead<BYTE>(plant + 0x141))
		return false;   // NotExist
	int px = MemSafeRead<int>(plant + 0x8);
	int pw = MemSafeRead<int>(plant + 0x10);
	int py = MemSafeRead<int>(plant + 0xC);
	if (pw <= 0 || pw > 400)
		return false;
	// ★ 渐隐/销毁基于物品自身剩余寿命：<=100（下次产前1秒）开始淡出，<=25 完全消失；
	//   已选中的物品（正在拖拽使用）豁免
	int remain = MgItemRemainCs(itemIdx);
	if (remain <= 25 && g_mgSelected != itemIdx)
		return false;
	// 槽位：同株产出物按 spawn 顺序排
	int slot = 0;
	for (int i = 0; i < g_mgItemCount; i++)
		if (g_mgItems[i].plant == plant && i < itemIdx)
			slot++;
	// 物品产生位置：相对原位置下移100px 右移40px
	int cx = px + pw / 2 + 40;
	int cy = py - 58 + 100 - slot * 42;   // 原 py-58 → 下移100 = py+42
	// 平滑浮动：仅 y 方向缓慢正弦 ±4px（周期约 3 秒），去掉 x 抖动
	int t = MgPlayingTime();
	cy += (int)(sinf(t * 0.02f + itemIdx * 1.7f) * 4.0f);
	*outCx = cx;
	*outCy = cy;
	return true;
}

// 产出物当前绘制档位：0=原图 1=半透明(a50) 2=更透明(a25) -1=完全消失（下次产前1s渐隐；选中物品不渐隐）
static int MgItemFadeLevel(int itemIdx)
{
	if (itemIdx < 0 || itemIdx >= g_mgItemCount)
		return -1;
	if (g_mgSelected == itemIdx)
		return 0;   // 选中（正在使用）不渐隐
	// ★ 用物品自身剩余寿命判断（不再读实时倒计时）
	int remain = MgItemRemainCs(itemIdx);
	if (remain <= 25)
		return -1;
	if (remain > 75)
		return 0;
	if (remain > 50)
		return 1;
	return 2;
}

// 当前选中产出物类型（-1=无）——高亮判定用
static int MgSelectedItemType()
{
	if (g_mgSelected < 0 || g_mgSelected >= g_mgItemCount)
		return -1;
	return g_mgItems[g_mgSelected].type;
}

// 留声机攻速加成系数（1.0=无加成；<1.0 表示更快的冷却）
static float MgBoostFactor(DWORD plantAddr)
{
	for (int i = 0; i < g_mgBoostCount; i++)
		if (g_mgBoosts[i].plant == plantAddr)
			return (float)(100 - g_mgBoostPercent) / 100.0f;
	return 1.0f;
}

// 播放使用音效
// ★ 用游戏音效函数 0x515020（eax=音效ID, ecx=[LawnApp+0x784], [esp]=float音量, ret 4），
//   与禅境花园施肥/浇水/留声机/杀虫剂同款（0x51EF/0x51F0 区反汇编确认）。
//   不要用 0x4560C0（那是 UI 音效路径，ID 表不同，播放的是不相关音效）。
// 音效 ID（禅境花园同款）：4D=浇水 51=施肥 54=杀虫剂 63=留声机
static void MgPlayUseSound(int type)
{
	int sid = (type == 0) ? 0x51 : (type == 1) ? 0x4D : (type == 2) ? 0x63 : 0x54;
	__asm {
		pushad
		mov ecx, 0x6A9EC0
		mov ecx, dword ptr [ecx]
		mov ecx, dword ptr [ecx+0x784]   ; ecx = AudioPlayer（zen 同款取法）
		mov eax, sid
		push 0x3F800000                   ; 音量 1.0f
		mov ebx, 0x515020
		call ebx
		popad
	}
}


// 创建"使用效果"动画 reanim 并登记定时清理
// ★ loopType 设 3（不循环播完停住）——设 2（播完消失）时若默认动画仅 1 帧会立即消失；
//   统一由轮询在 1.5 秒后 Die（0x4733F0，this=ecx）。
// type: 0肥料 2留声机 3杀虫剂；水壶单独走 MgApplyWater
static void MgPlayUseAnim(int type, int cx, int cy, int layer)
{
	int animType = (type == 0) ? (int)AnimationType::Fertilizer
		: (type == 2) ? (int)AnimationType::Phonograph
		: (type == 3) ? (int)AnimationType::Spray : -1;
	if (animType < 0)
		return;
	// 释放位置偏移：肥料左移40上移70 / 留声机左移5上移10 / 杀虫剂上移60
	int dx = 0, dy = 0;
	if (type == 0) { dx = -40; dy = -70; }
	else if (type == 2) { dx = -5; dy = -10; }
	else if (type == 3) { dy = -60; }
	__try
	{
		DWORD reanim = MgCreateReanim(animType, (float)(cx + dx), (float)(cy + dy), layer + 2);
		if (reanim)
		{
			if (type == 3)
			{
				// ★ 渲染到僵尸图层上层：reanim+0x64 = renderGroup（byte，组号越大越上层）。
				//   游戏创建植物/僵尸 reanim 时设 1（0x40BC53 实证）；我们经 0x453C30 创建默认 0
				//   → 杀虫剂被植物/僵尸盖住。设 2 → 严格在植物/僵尸组之上。
				MemSafeWrite<BYTE>(reanim + 0x64, 2);
			}
			// 0x10=loopType：杀虫剂=0(循环播放直到杀虫剂结束)；其他=3(播完停住)
			int loopType = (type == 3) ? 0 : 3;
			MemSafeWrite<int>(reanim + 0x10, loopType);
			if (g_mgFxCount < 16)
			{
				g_mgFxAnims[g_mgFxCount].addr = reanim;
				// 杀虫剂动画持续到杀虫剂区域结束（与 MgSprayDurationCs 同步）；其他 1.5 秒
				g_mgFxAnims[g_mgFxCount].endCs = MgPlayingTime()
					+ ((type == 3) ? g_mgSprayDurationCs : 150);
				g_mgFxCount++;
			}
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 立即销毁 reanim（0x4733F0，this=ecx）
static void MgKillReanim(DWORD addr)
{
	if (!addr)
		return;
	__asm {
		pushad
		mov ecx, addr
		mov ebx, 0x4733F0
		call ebx
		popad
	}
}

// ==================== 西瓜投手升级路线选择：实现 ====================
// （设计说明见前文"西瓜投手升级路线选择"状态段；本段依赖 MgCreateReanim/MgKillReanim）

// UTF-8 → GBK（游戏 1051 中文版按代码页 936 渲染文本；本工程 /utf-8 编译，字面量为 UTF-8）
static void MelonUtf8ToGbk(const char* utf8, char* out, int outLen)
{
	wchar_t wide[256];
	out[0] = 0;
	int wn = MultiByteToWideChar(CP_UTF8, 0, utf8, -1, wide, 256);
	if (wn <= 0)
		return;
	WideCharToMultiByte(936, 0, wide, -1, out, outLen, 0, 0);
}

// 底部字幕条提示（截图那种大字幕条）。
// 直接调 MessageWidget::SetLabel(0x459010)：ecx=MessageStyle, edx=const std::string&, esi=widget；
// widget 取 Board+0x140（DisplayAdviceAgain 0x40CA35 反汇编实证 [edi+0x140]=MessageWidget*）。
// 样式 0xC=12：与原版 1-1 教程"点击落下的阳光收集它"同款大字幕条（0x40c685 调用点实证）。
// std::string 用栈上 0x20 字节缓冲 + 游戏构造函数 0x404450 构造、0x404420 析构
// （实测布局：+0x14=长度、+0x18=容量(0xF=SSO)，对象 0x1C 字节；SetLabel 内部拷贝字符串，临时对象可立即析构）。
// ★ 不走 Board::DisplayAdviceAgain：其 theHelpIndex 直接作下标写 Board+0x55A8 标志数组（约 0x44 字节），
//   传自定义大编号会越界写 Board，故绕开。
static void MelonShowAdvice(DWORD boardAddr, const char* gbkText)
{
	DWORD mw = MemSafeRead<DWORD>(boardAddr + 0x140);
	if (mw < 0x10000)
		return;
	// ★进关瞬间 MessageWidget 可能尚未初始化完成：SetLabel 会写 [mw+0x298]/[mw+0x318]，
	//   widget 未就绪时直接跳过（下帧轮询重试，notified 已置位不会重弹）
	if (!CrashIsReadable(mw, 0x320))
		return;
	__asm {
		pushad
		sub esp, 0x20
		mov ecx, esp        ; ecx = 栈上 string 对象
		push gbkText
		mov ebx, 0x404450
		call ebx            ; std::string::basic_string(const char*)，thiscall callee 清 4
		mov edx, esp        ; edx = &string
		mov ecx, 0x0C       ; MessageStyle 12（大字幕条）
		mov esi, mw
		mov ebx, 0x459010
		call ebx            ; MessageWidget::SetLabel
		mov ecx, esp
		mov ebx, 0x404420
		call ebx            ; std::string::~basic_string
		add esp, 0x20
		popad
	}
}

// 世界通道隐身：全部轨道渲染组改为 7。
// 轨道实例数组 [reanim+0x58]，个数 [[reanim+0xC]+4]，stride 0x60，轨道渲染组 @ +0x48
// （DrawRenderGroup 0x472E40 反汇编：cmp [edi+0x48], edx 逐轨道比对组号，世界通道只画组 0）。
static void MelonReanimHideFromWorld(DWORD reanim)
{
	if (!reanim)
		return;
	DWORD def = MemSafeRead<DWORD>(reanim + 0xC);
	DWORD tracks = MemSafeRead<DWORD>(reanim + 0x58);
	if (def < 0x10000 || tracks < 0x10000)
		return;
	int count = MemSafeRead<int>(def + 4);
	if (count < 0 || count > 64)
		return;
	for (int i = 0; i < count; i++)
		MemSafeWrite<int>(tracks + i * 0x60 + 0x48, 7);
}

// 在 UI 层（DrawUITop 的 Graphics*）绘制 reanim：手动 DrawRenderGroup(7, g)
// （0x472E40：ecx=reanim，push 组号、push g，被调用者 ret 8 清栈）
static void MelonDrawReanimUI(DWORD reanim, DWORD g)
{
	if (!reanim)
		return;
	// 悬空防护：reanim 已被释放（堆页失效）时读 +0x14 本身就会踩空
	if (!CrashIsReadable(reanim, 0x100))
		return;
	if (MemSafeRead<BYTE>(reanim + 0x14))
		return;   // NotExist
	__asm {
		pushad
		push 7              ; 渲染组 7（世界通道画不到的自定义组）
		push g
		mov ecx, reanim
		mov ebx, 0x472E40
		call ebx
		popad
	}
}

// 创建待机动画：MgCreateReanim(类型,x,y,layer) + SetFramesForLayer("anim_idle")(0x473280，
// push 轨道名、ecx=reanim、ret 4) + loopType(+0x10)=0（循环，MgPlayUseAnim 实证 0=循环播放）
// + 全轨道渲染组改 7（世界通道隐身，由 MelonDrawReanimUI 在 UI 层手绘）。
static DWORD MelonCreateIdleReanim(int animType, float x, float y)
{
	DWORD reanim = MgCreateReanim(animType, x, y, 0x310000);
	if (!reanim)
		return 0;
	__try
	{
		__asm {
			pushad
			push offset g_melIdleTrack   ; "anim_idle"（Melonpult/WinterMelon.reanim 均有此轨道）
			mov ecx, reanim
			mov ebx, 0x473280
			call ebx                     ; Reanimation::SetFramesForLayer
			popad
		}
		MemSafeWrite<int>(reanim + 0x10, 0);   // loopType 0=循环
		MelonReanimHideFromWorld(reanim);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		return 0;
	}
	return reanim;
}

// 加载面板贴图（__try 防护，与 LoadExpPouchImages 同模式）
static void MelonLoadImages()
{
	__try
	{
		DWORD isNew = 0;
		Draw::PString fn = Draw::ToString("images\\ChooseUpgradeDirection.png");
		Draw::PString variant = Draw::ToString("");
		DWORD ref = Draw::GetSharedImage(isNew, variant, fn);
		if (ref != 0)
			g_melPanelImage = Draw::SharedImageRefToImage(ref);
		// 方案按钮：原版对话框按钮三块切片（左/中/右 + 按下态，36/46/35×46）
		isNew = 0;
		Draw::PString fnBtn = Draw::ToString("images\\button_left.png");
		DWORD refBtn = Draw::GetSharedImage(isNew, variant, fnBtn);
		if (refBtn != 0)
			g_melBtnL = Draw::SharedImageRefToImage(refBtn);
		isNew = 0;
		fnBtn = Draw::ToString("images\\button_middle.png");
		refBtn = Draw::GetSharedImage(isNew, variant, fnBtn);
		if (refBtn != 0)
			g_melBtnM = Draw::SharedImageRefToImage(refBtn);
		isNew = 0;
		fnBtn = Draw::ToString("images\\button_right.png");
		refBtn = Draw::GetSharedImage(isNew, variant, fnBtn);
		if (refBtn != 0)
			g_melBtnR = Draw::SharedImageRefToImage(refBtn);
		isNew = 0;
		fnBtn = Draw::ToString("images\\button_down_left.png");
		refBtn = Draw::GetSharedImage(isNew, variant, fnBtn);
		if (refBtn != 0)
			g_melBtnDownL = Draw::SharedImageRefToImage(refBtn);
		isNew = 0;
		fnBtn = Draw::ToString("images\\button_down_middle.png");
		refBtn = Draw::GetSharedImage(isNew, variant, fnBtn);
		if (refBtn != 0)
			g_melBtnDownM = Draw::SharedImageRefToImage(refBtn);
		isNew = 0;
		fnBtn = Draw::ToString("images\\button_down_right.png");
		refBtn = Draw::GetSharedImage(isNew, variant, fnBtn);
		if (refBtn != 0)
			g_melBtnDownR = Draw::SharedImageRefToImage(refBtn);
		// 文字贴图（方案A/B + 说明文字，缺图回退 GBK 文字绘制）
		isNew = 0;
		Draw::PString fnTA = Draw::ToString("images\\RouteBtnA.png");
		DWORD refTA = Draw::GetSharedImage(isNew, variant, fnTA);
		if (refTA != 0)
			g_melBtnTextA = Draw::SharedImageRefToImage(refTA);
		isNew = 0;
		Draw::PString fnTB = Draw::ToString("images\\RouteBtnB.png");
		DWORD refTB = Draw::GetSharedImage(isNew, variant, fnTB);
		if (refTB != 0)
			g_melBtnTextB = Draw::SharedImageRefToImage(refTB);
		isNew = 0;
		Draw::PString fnDA = Draw::ToString("images\\ChooseMelon.png");
		DWORD refDA = Draw::GetSharedImage(isNew, variant, fnDA);
		if (refDA != 0)
			g_melTextDescA = Draw::SharedImageRefToImage(refDA);
		isNew = 0;
		Draw::PString fnDB = Draw::ToString("images\\ChooseWinterMelon.png");
		DWORD refDB = Draw::GetSharedImage(isNew, variant, fnDB);
		if (refDB != 0)
			g_melTextDescB = Draw::SharedImageRefToImage(refDB);
		g_melImagesLoaded = true;
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_melImagesLoaded = false;   // 下一帧重试
	}
}

// 收场：杀掉自己创建的两个 reanim 并复位窗口状态。
// ★ boardAddr 用于防悬空：boardAddr 与开窗时的 Board 不一致（换关）时只清状态不杀 reanim
//   （关卡拆除流程会连带销毁 reanim，再杀=use-after-free；传 0 同样只清状态）。
static void MelonKillChooser(DWORD boardAddr)
{
	if (boardAddr != 0 && boardAddr == g_melBoardAddr)
	{
		// ★只杀仍然合法的 reanim：地址可读且 NotExist==0 才调 KillReanim。
		//   修改器/关卡拆除改变堆布局时，悬空调 Die = use-after-free（进关崩溃嫌疑路径）。
		if (g_melReanimMelon && CrashIsReadable(g_melReanimMelon, 0x100)
			&& !MemSafeRead<BYTE>(g_melReanimMelon + 0x14))
			MgKillReanim(g_melReanimMelon);
		if (g_melReanimWinter && CrashIsReadable(g_melReanimWinter, 0x100)
			&& !MemSafeRead<BYTE>(g_melReanimWinter + 0x14))
			MgKillReanim(g_melReanimWinter);
	}
	g_melReanimMelon = 0;
	g_melReanimWinter = 0;
	g_melUIActive = false;
	g_melPhase = 0;
	g_melPlantAddr = 0;
	g_melBoardAddr = 0;
}

// 打开选择窗口（右键卡 3 阶西瓜时调用）
static void MelonOpenChooser(DWORD plantAddr, DWORD boardAddr)
{
	if (g_melUIActive)
		return;   // 已开窗：忽略（一次只处理一株）
	int slot = MelonGetSlot(plantAddr);
	if (slot < 0 || g_melSlots[slot].route != 0)
		return;
	auto it = g_plantExperience.find(plantAddr);
	int exp = (it != g_plantExperience.end()) ? it->second : 0;
	const auto& t = GetSeedTierThresholds((int)SeedType::Melonpult);
	if (exp < t[3])
		return;   // 未达 3 阶阈值：不开窗

	// 创建两个待机动画（初始位置在屏外，绘制循环里跟随面板滑动更新）
	float ax = (float)(-MEL_PANEL_W + MEL_ANIM_X);
	DWORD rm = MelonCreateIdleReanim((int)AnimationType::Melonpult, ax, (float)MEL_ANIM1_Y);
	DWORD rw = MelonCreateIdleReanim((int)AnimationType::WinterMelon, ax, (float)MEL_ANIM2_Y);
	if (!rm || !rw)
	{
		// 创建失败（任一）：把已创建的杀掉，不开窗（下次右键重试）
		if (rm) MgKillReanim(rm);
		if (rw) MgKillReanim(rw);
		return;
	}
	g_melReanimMelon = rm;
	g_melReanimWinter = rw;
	g_melPlantAddr = plantAddr;
	g_melBoardAddr = boardAddr;
	g_melSlideX = -MEL_PANEL_W;
	g_melPhase = 1;
	g_melUIActive = true;
}

// 右键命中西瓜（UpdateMarigoldFrameInner 右键检测段调用）
static void MelonOnRightClick(DWORD plantAddr, DWORD boardAddr)
{
	if (g_melUIActive)
		return;
	MelonOpenChooser(plantAddr, boardAddr);
}

// 选择窗口激活期间处理左键（HandleExpPouchMouseDown 开头调用；返回 1 = 已消费/拦截）
static int HandleMelonChooserMouseDown(DWORD boardAddr, int x, int y)
{
	if (!g_melUIActive)
		return 0;

	// 放行右上角主菜单按钮（允许选择期间暂停；Board+0x148=菜单按钮 Widget*，含范围校验回退）
	int mx = 742, my = 8, mw2 = 60, mh2 = 57;
	DWORD menuW = MemSafeRead<DWORD>(boardAddr + 0x148);
	if (menuW >= 0x10000)
	{
		int mmx = MemSafeRead<int>(menuW + 0x0);
		int mmy = MemSafeRead<int>(menuW + 0x4);
		int mmw = MemSafeRead<int>(menuW + 0x8);
		int mmh = MemSafeRead<int>(menuW + 0xC);
		if (mmx >= 600 && mmx <= 790 && mmy >= 0 && mmy <= 120
			&& mmw >= 30 && mmw <= 120 && mmh >= 30 && mmh <= 120)
		{
			mx = mmx; my = mmy; mw2 = mmw; mh2 = mmh;
		}
	}
	if (x >= mx && x <= mx + mw2 && y >= my && y <= my + mh2)
		return 0;   // 菜单按钮：放行原版

	// 停留期：命中方案按钮 → 记录路线并开始滑出
	if (g_melPhase == 2)
	{
		bool inBtn1 = (x >= MEL_BTN_X && x <= MEL_BTN_X + MEL_BTN_W
			&& y >= MEL_BTN1_Y && y <= MEL_BTN1_Y + MEL_BTN_H);
		bool inBtn2 = (x >= MEL_BTN_X && x <= MEL_BTN_X + MEL_BTN_W
			&& y >= MEL_BTN2_Y && y <= MEL_BTN2_Y + MEL_BTN_H);
		if (inBtn1 || inBtn2)
		{
			int slot = MelonGetSlot(g_melPlantAddr);
			if (slot >= 0)
				g_melSlots[slot].route = inBtn1 ? 1 : 2;
			// 方案B（冰瓜路线）：滑出收场后在帧更新里替换为冰西瓜、经验全带走
			if (!inBtn1 && g_melPlantAddr)
			{
				g_melPendingReplaceAddr = g_melPlantAddr;
				g_melPendingBoardAddr = boardAddr;
				g_melPendingRow = MemSafeRead<int>(g_melPlantAddr + 0x1C);   // Row
				g_melPendingCol = MemSafeRead<int>(g_melPlantAddr + 0x28);   // Column
				auto itE = g_plantExperience.find(g_melPlantAddr);
				g_melPendingExp = (itE != g_plantExperience.end()) ? itE->second : 0;
			}
			g_melPhase = 3;   // 面板+动画整体向左滑出；等阶随即解锁（显示/攻速按真实等阶）
			return 1;
		}
	}

	// 滑入/停留/滑出期间：吞掉其余所有左键，防止误种/误铲/误点经验包
	return 1;
}

// 消息横幅下移：样式 12 的 Y 硬编码在 MessageWidget::Draw 0x459B08
// （mov ebp, 0x12C=300px；字节 bd 2c 01 00 00，两条绘制路径 reanim/普通文本都用此值）。
// 改立即数为 0x12C+偏移。★样式 13 与 12 共用此分支，同受影响（原版样式13少用）。
static bool g_melBannerYPatched = false;
static void MelonPatchBannerY()
{
	if (g_melBannerYPatched)
		return;
	DWORD cur = MemSafeRead<DWORD>(0x459B09);
	DWORD want = (DWORD)(0x12C + MEL_BANNER_Y_OFFSET);
	if (cur == want)
	{
		g_melBannerYPatched = true;   // 已是目标值（重复调用/热重载）
	}
	else if (cur == 0x0000012C)     // 未打补丁的原始立即数，字节校验通过才写
	{
		MemSafeWrite<DWORD>(0x459B09, want);
		g_melBannerYPatched = true;
	}
	// 其他值：字节不认识，不动（下帧重读，无害）
}


// 每帧轮询（onGameObjectsUpdate 调用）：
//   ① 首次加载面板贴图
//   ② 遍历场上西瓜：经验首次达到 T3 → 底部字幕条提示一次（每株只提示一次）
//   ③ 窗口激活时的状态校验（换关 / 植物死亡 / reanim 意外消失 → 收场不升级）
static void UpdateMelonChooseFrame(DWORD boardAddr)
{
	CRASH_STEP("melon:enter");
	MelonPatchBannerY();
	CRASH_STEP("melon:patch");
	if (boardAddr < 0x10000)
		return;   // Board 无效（换关间隙）：后续全要读 board 字段，直接跳过
	if (!g_melImagesLoaded && ImageLoadRetryAllowed(5))   // ★ 限流：防失败后每帧重试（每帧漏 ≥1KB）
		MelonLoadImages();
	CRASH_STEP("melon:images");

	// 换关检测：Board 变了 → 旧 reanim 已随旧关销毁，只清状态
	if (g_melUIActive && boardAddr != g_melBoardAddr)
	{
		MelonKillChooser(0);
		return;
	}

	// 方案B执行：窗口已收场（g_melUIActive=false）→ 替换为冰西瓜、经验全带走
	// 流程与"向日葵5阶升级为双子向日葵"完全同款：清旧经验防 onPlantRemove 分配 →
	// Remove 旧植物 → CreatePlant 新植物 → 经验写到新地址
	// ★绑定发生时的 Board：换关（含 Board 地址复用相同值）即作废，防悬空地址误替换
	if (g_melPendingReplaceAddr && !g_melUIActive)
	{
		if (g_melPendingBoardAddr != boardAddr)
		{
			g_melPendingReplaceAddr = 0;   // 跨关作废
		}
		else
		{
			PVZ::Plant oldPlant(g_melPendingReplaceAddr);
			if (oldPlant.isValid() && !oldPlant.NotExist)
			{
				g_plantExperience[g_melPendingReplaceAddr] = 0;   // 防止 onPlantRemove 分配出去
				oldPlant.Remove();
				PVZ::Plant newPlant = Creator::CreatePlant(SeedType::WinterMelon,
					g_melPendingRow, (byte)g_melPendingCol);
				int newAddr = newPlant.GetBaseAddress();
				if (newAddr)
					g_plantExperience[newAddr] = g_melPendingExp;
			}
			g_melPendingReplaceAddr = 0;
		}
	}
	CRASH_STEP("melon:pending");

	const auto& t = GetSeedTierThresholds((int)SeedType::Melonpult);
	int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
	int plantCount = MemSafeRead<int>(boardAddr + 0xB0);

	// ★槽位剪枝：清掉死亡/铲除西瓜的槽位（防地址复用串档：新西瓜继承旧 route/notified）
	MelonPruneSlots(plantArray, plantCount);

	// ② 扫描西瓜提示（暂停时不弹，notified 仍置位防恢复后连弹）
	if (plantArray && plantCount > 0
		&& !MemSafeRead<BYTE>(boardAddr + 0x164))
	{
		CRASH_STEP("melon:scan");
		for (int i = 0; i < plantCount; i++)
		{
			DWORD p = plantArray + i * 0x14C;
			if (MemSafeRead<BYTE>(p + 0x141)) continue;   // NotExist
			if (MemSafeRead<int>(p + 0x24) != (int)SeedType::Melonpult) continue;
			if (MelonGetRoute(p) != 0) continue;
			int slot = MelonGetSlot(p);
			if (slot < 0 || g_melSlots[slot].notified) continue;
			auto it = g_plantExperience.find(p);
			int exp = (it != g_plantExperience.end()) ? it->second : 0;
			if (exp < t[3]) continue;
			g_melSlots[slot].notified = 1;
			char utf8[192];
			sprintf_s(utf8, sizeof(utf8), "你的一株西瓜投手已经达到%d经验，试试右击它吧", t[3]);
			char gbk[256];
			MelonUtf8ToGbk(utf8, gbk, sizeof(gbk));
			MelonShowAdvice(boardAddr, gbk);
			break;   // 一帧最多弹一条
		}
	}

	// ③ 窗口状态校验
	if (!g_melUIActive)
		return;
	CRASH_STEP("melon:alive");

	// 待选植物死亡/消失 → 收场不升级
	bool plantAlive = false;
	if (plantArray && plantCount > 0)
	{
		for (int i = 0; i < plantCount; i++)
		{
			DWORD p = plantArray + i * 0x14C;
			if (p == g_melPlantAddr && !MemSafeRead<BYTE>(p + 0x141))
			{
				plantAlive = true;
				break;
			}
		}
	}
	if (!plantAlive)
	{
		MelonKillChooser(boardAddr);
		return;
	}
	// reanim 意外消失（被游戏回收/堆页已失效）→ 收场
	// ★可读性先于内容：reanim 被释放后读 +0x14 本身可能踩空页
	if (!g_melReanimMelon || !g_melReanimWinter
		|| !CrashIsReadable(g_melReanimMelon, 0x100)
		|| !CrashIsReadable(g_melReanimWinter, 0x100)
		|| MemSafeRead<BYTE>(g_melReanimMelon + 0x14)
		|| MemSafeRead<BYTE>(g_melReanimWinter + 0x14))
	{
		MelonKillChooser(boardAddr);
		return;
	}
}

// 选择窗口绘制（onDrawUITop 调用，屏幕空间顶层）
//   phase1 滑入 → phase2 停留（显示按钮）→ 点按钮 phase3 滑出 → 收场
//   动画跟随面板：每帧写 reanim mX(+0x2C)/mY(+0x38) = slideX + 面板内锚点
static void DrawMelonChooseUI()
{
	if (!g_melUIActive)
		return;
	CRASH_STEP("melon:draw");
	// 与 DrawExpPouchUI 同款防御：Graphics* 从堆存储读取 + 有效性校验
	DWORD g = (g_expPouchGStore != 0)
		? MemSafeRead<DWORD>(g_expPouchGStore) : 0;
	if (!g || !ExpPouchGraphicsValid(g))
		return;
	int pvzBase = MemSafeRead<int>(0x6A9EC0);
	if (pvzBase < 0x400000)
		return;
	int boardAddr = MemSafeRead<int>(pvzBase + 0x768);
	if (!boardAddr)
		return;

	// 滑动推进（渲染帧驱动；暂停时冻结）
	if (!MemSafeRead<BYTE>(boardAddr + 0x164))
	{
		if (g_melPhase == 1)
		{
			g_melSlideX += MEL_SLIDE_STEP;
			if (g_melSlideX >= 0) { g_melSlideX = 0; g_melPhase = 2; }
		}
		else if (g_melPhase == 3)
		{
			g_melSlideX -= MEL_SLIDE_STEP + 4;   // 滑出略快于滑入
			if (g_melSlideX <= -MEL_PANEL_W - 20)
			{
				MelonKillChooser(boardAddr);
				return;
			}
		}
	}

	// 动画跟随面板（写 reanim 位置字段 mX/mY，pvzclass 命名 XOffset/YOffset）
	float ax = (float)(g_melSlideX + MEL_ANIM_X);
	if (g_melReanimMelon)
	{
		MemSafeWrite<float>(g_melReanimMelon + 0x2C, ax);
		MemSafeWrite<float>(g_melReanimMelon + 0x38, (float)MEL_ANIM1_Y);
	}
	if (g_melReanimWinter)
	{
		MemSafeWrite<float>(g_melReanimWinter + 0x2C, ax);
		MemSafeWrite<float>(g_melReanimWinter + 0x38, (float)MEL_ANIM2_Y);
	}

	__try
	{
		// 面板（303x600 纵向满窗口，从左滑入）
		if (g_melPanelImage)
			Draw::DrawImage(g_melSlideX, 0, g_melPanelImage, g);

		// 两个待机动画画在面板之上（渲染组 7 在 UI 层手动绘制）
		MelonDrawReanimUI(g_melReanimMelon, g);
		MelonDrawReanimUI(g_melReanimWinter, g);

		// 右下方两个按钮（窗口外；停留期与滑出前半段显示）
		if (g_melPhase == 2 || (g_melPhase == 3 && g_melSlideX > -MEL_PANEL_W / 2))
		{
			// 悬停检测：复用 Board::MouseMove hook 写入的鼠标坐标（经验包 UI 同源）
			ExpPouchUpdateMousePos();
			for (int b = 0; b < 2; b++)
			{
				int bx = MEL_BTN_X;
				int by = (b == 0) ? MEL_BTN1_Y : MEL_BTN2_Y;
				bool hover = (g_expPouchMouseX >= bx && g_expPouchMouseX < bx + MEL_BTN_W
					&& g_expPouchMouseY >= by && g_expPouchMouseY < by + MEL_BTN_H);
				// 三块式拼装：左帽 + 中段平铺 + 右帽（悬停=button_down_* 按下态切片）
				DWORD bl = (hover && g_melBtnDownL) ? g_melBtnDownL : g_melBtnL;
				DWORD bm = (hover && g_melBtnDownM) ? g_melBtnDownM : g_melBtnM;
				DWORD br = (hover && g_melBtnDownR) ? g_melBtnDownR : g_melBtnR;
				int nMid = (MEL_BTN_W - 36 - 35) / 46;
				if (nMid < 1) nMid = 1;
				if (bl)  Draw::DrawImage(bx, by, bl, g);
				for (int m = 0; m < nMid; m++)
					if (bm) Draw::DrawImage(bx + 36 + m * 46, by, bm, g);
				if (br)  Draw::DrawImage(bx + 36 + nMid * 46, by, br, g);
				// 按钮文字：优先贴图（自动居中于 163x46 按钮），缺图回退 GBK 文字
				DWORD btnText = (b == 0) ? g_melBtnTextA : g_melBtnTextB;
				if (btnText)
				{
					int tw = (int)MemSafeRead<float>(btnText + 0x10);
					int th = (int)MemSafeRead<float>(btnText + 0x14);
					// 自动居中后整体左移64、上移20（用户定稿位置）
					Draw::DrawImage(bx + (MEL_BTN_W - tw) / 2 - 64, by + (MEL_BTN_H - th) / 2 - 20, btnText, g);
				}
				else
				{
					char gbkBtn[32];
					MelonUtf8ToGbk(b == 0 ? "方案A" : "方案B", gbkBtn, sizeof(gbkBtn));
					MelonSetFont(g);
					NativeDrawExpText(g, bx + 63, by + 16, gbkBtn, 255, 240, 180);
				}
			}
			// 两条说明文字：优先贴图，缺图回退 GBK 文字
			if (g_melTextDescA)
				Draw::DrawImage(MEL_TEXT1_X, MEL_TEXT1_Y, g_melTextDescA, g);
			else
			{
				char gbk1[32];
				MelonUtf8ToGbk("A：极致的输出", gbk1, sizeof(gbk1));
				MelonSetFont(g);
				NativeDrawExpText(g, MEL_TEXT1_X, MEL_TEXT1_Y, gbk1, 151, 81, 18);
			}
			if (g_melTextDescB)
				Draw::DrawImage(MEL_TEXT2_X, MEL_TEXT2_Y, g_melTextDescB, g);
			else
			{
				char gbk2[32];
				MelonUtf8ToGbk("B：强大的群控", gbk2, sizeof(gbk2));
				MelonSetFont(g);
				NativeDrawExpText(g, MEL_TEXT2_X, MEL_TEXT2_Y, gbk2, 151, 81, 18);
			}
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		// 绘制异常静默跳过（不崩溃）
	}
}

// 水壶：回血 + 水壶动画（Kettle reanim，播完自灭）
static void MgApplyWater(DWORD target)
{
	if (!target)
		return;
	PVZ::Plant p(target);
	if (!p.isValid())
		return;
	int hp = (int)p.Hp, maxhp = (int)p.MaxHp;
	if (maxhp > 0 && hp < maxhp)
		p.Hp = min(hp + g_mgWaterHeal, maxhp);
	__try
	{
		// 位置取植物中心（ImageX+W/2, ImageY+H/2），动画在植物身上播放
		int px = MemSafeRead<int>(target + 0x8);
		int py = MemSafeRead<int>(target + 0xC);
		int pw = MemSafeRead<int>(target + 0x10);
		int ph = MemSafeRead<int>(target + 0x14);
		int layer = MemSafeRead<int>(target + 0x20);
		if (pw <= 0 || pw > 400 || ph <= 0 || ph > 400)
			return;
		DWORD reanim = MgCreateReanim((int)AnimationType::Kettle,
			(float)(px + pw / 2 - 10), (float)(py + ph / 2 - 40), layer + 2);   // 水壶释放：左移10 上移40
		if (reanim)
		{
			MemSafeWrite<int>(reanim + 0x10, 3);   // 0x10=loopType，3=不循环播完停住
			MgHideGoldTrack(reanim);   // ★ Kettle reanim 含普通水壶+金水壶两个轨道，只保留普通水壶
			if (g_mgFxCount < 16)
			{
				g_mgFxAnims[g_mgFxCount].addr = reanim;
				g_mgFxAnims[g_mgFxCount].endCs = MgPlayingTime() + 150;
				g_mgFxCount++;
			}
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 留声机：登记/刷新攻速加成
static void MgApplyBoost(DWORD target)
{
	if (!target)
		return;
	int endCs = MgPlayingTime() + g_mgBoostDurationCs;
	for (int i = 0; i < g_mgBoostCount; i++)
	{
		if (g_mgBoosts[i].plant == target)
		{
			g_mgBoosts[i].endCs = endCs;
			return;
		}
	}
	if (g_mgBoostCount < MG_MAX_BOOSTS)
	{
		g_mgBoosts[g_mgBoostCount].plant = target;
		g_mgBoosts[g_mgBoostCount].endCs = endCs;
		g_mgBoostCount++;
	}
}

// 杀虫剂：登记一个格子伤害区域
static void MgApplySpray(int row, int col, DWORD source)
{
	if (row < 0 || row > 5 || col < 0 || col > 8)
		return;
	if (g_mgSprayCount < MG_MAX_SPRAYS)
	{
		g_mgSprays[g_mgSprayCount].row = row;
		g_mgSprays[g_mgSprayCount].col = col;
		g_mgSprays[g_mgSprayCount].source = source;
		g_mgSprays[g_mgSprayCount].startCs = MgPlayingTime();
		g_mgSprays[g_mgSprayCount].ticks = 0;
		g_mgSprayCount++;
	}
	MgPlayUseSound(3);
}

// 使用选中的产出物；返回 true=已消耗（移除该产出物）
static bool MgUseSelectedItem(DWORD boardAddr, int x, int y)
{
	if (g_mgSelected < 0 || g_mgSelected >= g_mgItemCount)
		return false;
	int type = g_mgItems[g_mgSelected].type;
	int itemIdx = g_mgSelected;
	DWORD source = g_mgItems[itemIdx].plant;

	if (type == 3)   // 杀虫剂：点击格子
	{
		int col = -1, row = -1;
		if (!ExpPouchPixelToGrid(boardAddr, x, y, &col, &row))
			return false;   // 地图外：不消耗
		MgApplySpray(row, col, source);
		// 杀虫剂动画：喷在格子中心
		PVZ::Board bd(boardAddr);
		if (bd.GetBaseAddress())
		{
			int gx = bd.GridToXPixel(row, col);
			int gy = bd.GridToYPixel(row, col);
			int layer = MemSafeRead<int>(source + 0x20);
			MgPlayUseAnim(3, gx + 40, gy + 40, layer);
		}
	}
	else             // 肥料/水壶/留声机：点击植物
	{
		int col = -1, row = -1;
		if (!ExpPouchPixelToGrid(boardAddr, x, y, &col, &row))
			return false;
		DWORD target = ExpPouchFindPlantAt(boardAddr, row, col);
		if (!target)
			return false;
		if (type == 0)
			AddPlantExperience(target, g_expPouchExpGain);   // 肥料：同经验包 +300 经验
		else if (type == 1)
			MgApplyWater(target);
		else
			MgApplyBoost(target);
		// 肥料/留声机使用动画（在目标植物中心）
		if (type == 0 || type == 2)
		{
			int tpx = MemSafeRead<int>(target + 0x8);
			int tpy = MemSafeRead<int>(target + 0xC);
			int tpw = MemSafeRead<int>(target + 0x10);
			int tph = MemSafeRead<int>(target + 0x14);
			int tlayer = MemSafeRead<int>(target + 0x20);
			if (tpw > 0 && tpw <= 400 && tph > 0 && tph <= 400)
				MgPlayUseAnim(type, tpx + tpw / 2, tpy + tph / 2, tlayer);
		}
		MgPlayUseSound(type);
	}

	// 消耗产出物
	g_mgSelected = -1;
	g_mgItems[itemIdx] = g_mgItems[g_mgItemCount - 1];
	g_mgItemCount--;
	return true;
}

// 金盏花产出物点击处理；返回 1=已消费本次点击
// 流程：单击产出物拾起 → 拖动（图标跟随鼠标）→ 单击目标生效 / 点空地取消
static int HandleMarigoldItemMouseDown(DWORD boardAddr, int x, int y)
{
	// 1) 已有选中的产出物：点击目标生效；点空地/非目标取消选中（产出物保留）
	if (g_mgSelected >= 0)
	{
		// 再点选中的产出物自身 = 取消选中（防误作用于下方植物）
		{
			int cx = 0, cy = 0;
			if (MgItemCenter(g_mgSelected, &cx, &cy)
				&& x >= cx - 22 && x <= cx + 22 && y >= cy - 22 && y <= cy + 22)
			{
				g_mgSelected = -1;
				return 1;
			}
		}
		if (MgUseSelectedItem(boardAddr, x, y))
			return 1;
		g_mgSelected = -1;
		return 1;
	}
	// 2) 点击悬浮产出物 → 拾起
	for (int i = 0; i < g_mgItemCount; i++)
	{
		int cx = 0, cy = 0;
		if (!MgItemCenter(i, &cx, &cy))
			continue;
		if (x >= cx - 22 && x <= cx + 22 && y >= cy - 22 && y <= cy + 22)
		{
			g_mgSelected = i;
			g_expPouchSelected = false;   // 与经验包互斥
			return 1;
		}
	}
	return 0;
}

// 0x45FB1D 产出 hook 回调（trampoline 直接 call，__cdecl）
// 参数：plant(edi), x(原[esp]=ImageX), y(原[esp+4]=ImageY), coinType(原[esp+8],1金2银)
// 返回：1=已消费（跳过原版产金币）；0=走原版
// ★ 运行在游戏执行流中：只做纯 POD 读写（崩溃铁律：禁 std::map/fopen/CRT）
static int __cdecl MarigoldProduceCheck(DWORD plant, int x, int y, int coinType)
{
	(void)x; (void)y; (void)coinType;   // 调用约定参数，本回调不需要
	if (!plant)
		return 0;
	if (MemSafeRead<int>(plant + 0x24) != (int)SeedType::Marigold)
		return 0;
	if (MemSafeRead<BYTE>(plant + 0x141))
		return 0;   // NotExist
	int pvzBase = MemSafeRead<int>(0x6A9EC0);
	if (pvzBase < 0x400000)
		return 0;
	// 禅境花园模式（0x27）/禅境花园(0x2B)/智慧树(0x32)走原版产金币（花园金盏花保持原味）
	{
		int gm = MemSafeRead<int>(pvzBase + 0x7F8);
		if (gm == 0x27 || gm == 0x2B || gm == 0x32)
			return 0;
	}
	// 形态决定产出物：0白=肥料 1蓝=水壶 2黄=留声机 3绿=杀虫剂
	MgSpawnItem(plant, MgGetForm(plant));
	return 1;
}

// 安装金盏花产出 hook @ 0x45FB1D（原 5 字节 E8 xx xx xx xx = call 0x40CB10）
// 到达时栈：[esp]=x [esp+4]=y [esp+8]=coinType [esp+0xC]=3；edi=植物；ecx=board
// trampoline：cmp [edi+0x24]==38 → PUSHAD 传参调 MarigoldProduceCheck → 返回值非0
//   则 add esp,0x10 清4参数跳 0x45FB22（跳过原 call）；否则执行原 call（重算 rel32）跳 0x45FB22
void InstallMarigoldProduceHook()
{
	DWORD hookAddr = 0x45FB1D;
	BYTE raw[5];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 5);
	if (raw[0] != 0xE8)
		return;   // 安全核对：必须是 call（版本不符直接跳过，绝不崩溃）
	{
		static const BYTE kExpected[5] = { 0xE8, 0xEE, 0xCF, 0xFA, 0xFF };
		if (memcmp(raw, kExpected, 5) != 0)
		{
			CrashStr("HOOKSKIP name=MarigoldProduce site=0x45FB1D (bytes changed - modifier?)\r\n");
			return;
		}
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return;

	BYTE tp[128];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };

	// [0x00] cmp dword [edi+0x24], 38（金盏花判定）
	tp[p++] = 0x83; tp[p++] = 0x7F; tp[p++] = 0x24; tp[p++] = 38;
	int jneNotMg = p;
	tp[p++] = 0x75; tp[p++] = 0x00;                       // jne → ORIG
	// PUSHAD
	tp[p++] = 0x60;
	// push coinType（1st push，读 [E+0x28]）
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x28;
	// push y（2nd push，读 [E+0x24]）
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x28;
	// push x（3rd push，读 [E+0x20]）
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x28;
	// push plant（4th push，读 [E-0xC+0xC]=[E+0x00]=EDI）
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x0C;
	// call MarigoldProduceCheck（__cdecl）
	int callOff = (int)&MarigoldProduceCheck - (tramp + p + 5);
	tp[p++] = 0xE8; put32(callOff);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x10;       // add esp, 0x10
	tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x1C; // mov [esp+0x1C], eax（写回 EAX 槽）
	tp[p++] = 0x61;                                       // POPAD
	tp[p++] = 0x85; tp[p++] = 0xC0;                       // test eax, eax
	int jzDoOrig = p;
	tp[p++] = 0x74; tp[p++] = 0x00;                       // jz → ORIG
	// SKIP：清 4 参数 + 跳 0x45FB22（继续函数流程，跳过原版产金币）
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x10;       // add esp, 0x10
	{ int off = (int)0x45FB22 - (tramp + p + 5); tp[p++] = 0xE9; put32(off); }
	// ORIG：原 call 0x40CB10（重算 rel32）+ 跳 0x45FB22
	int origPos = p;
	*(BYTE*)(tp + jneNotMg + 1) = (BYTE)(origPos - (jneNotMg + 2));
	*(BYTE*)(tp + jzDoOrig + 1) = (BYTE)(origPos - (jzDoOrig + 2));
	tp[p++] = 0xE8;
	int rel = (int)0x40CB10 - (tramp + p + 4);
	put32(rel);
	{ int off = (int)0x45FB22 - (tramp + p + 5); tp[p++] = 0xE9; put32(off); }

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
}

// 加载产出物图片（禅境花园素材，__try 独立函数避 C2712）
static void LoadMarigoldImages()
{
	__try
	{
		DWORD isNew = 0;
		Draw::PString variant = Draw::ToString("");
		Draw::PString fn0 = Draw::ToString("images\\Fertilizer.png");
		DWORD r0 = Draw::GetSharedImage(isNew, variant, fn0);
		if (r0) g_mgImgFertilizer = Draw::SharedImageRefToImage(r0);
		Draw::PString fn1 = Draw::ToString("images\\WateringCan.png");
		DWORD r1 = Draw::GetSharedImage(isNew, variant, fn1);
		if (r1) g_mgImgWater = Draw::SharedImageRefToImage(r1);
		Draw::PString fn2 = Draw::ToString("images\\Phonograph.png");
		DWORD r2 = Draw::GetSharedImage(isNew, variant, fn2);
		if (r2) g_mgImgPhono = Draw::SharedImageRefToImage(r2);
		Draw::PString fn3 = Draw::ToString("images\\bug_spray.png");
		DWORD r3 = Draw::GetSharedImage(isNew, variant, fn3);
		if (r3) g_mgImgSpray = Draw::SharedImageRefToImage(r3);
		// 渐隐 alpha 档位图（python 生成：原图 alpha 50%/25%）
		Draw::PString fa50 = Draw::ToString("images\\MgFade_Fertilizer_a50.png");
		DWORD ra50 = Draw::GetSharedImage(isNew, variant, fa50);
		if (ra50) g_mgImgFertA50 = Draw::SharedImageRefToImage(ra50);
		Draw::PString fa25 = Draw::ToString("images\\MgFade_Fertilizer_a25.png");
		DWORD ra25 = Draw::GetSharedImage(isNew, variant, fa25);
		if (ra25) g_mgImgFertA25 = Draw::SharedImageRefToImage(ra25);
		Draw::PString wa50 = Draw::ToString("images\\MgFade_WateringCan_a50.png");
		DWORD rw50 = Draw::GetSharedImage(isNew, variant, wa50);
		if (rw50) g_mgImgWaterA50 = Draw::SharedImageRefToImage(rw50);
		Draw::PString wa25 = Draw::ToString("images\\MgFade_WateringCan_a25.png");
		DWORD rw25 = Draw::GetSharedImage(isNew, variant, wa25);
		if (rw25) g_mgImgWaterA25 = Draw::SharedImageRefToImage(rw25);
		Draw::PString pa50 = Draw::ToString("images\\MgFade_Phonograph_a50.png");
		DWORD rp50 = Draw::GetSharedImage(isNew, variant, pa50);
		if (rp50) g_mgImgPhonoA50 = Draw::SharedImageRefToImage(rp50);
		Draw::PString pa25 = Draw::ToString("images\\MgFade_Phonograph_a25.png");
		DWORD rp25 = Draw::GetSharedImage(isNew, variant, pa25);
		if (rp25) g_mgImgPhonoA25 = Draw::SharedImageRefToImage(rp25);
		Draw::PString ba50 = Draw::ToString("images\\MgFade_BugSpray_a50.png");
		DWORD rb50 = Draw::GetSharedImage(isNew, variant, ba50);
		if (rb50) g_mgImgSprayA50 = Draw::SharedImageRefToImage(rb50);
		Draw::PString ba25 = Draw::ToString("images\\MgFade_BugSpray_a25.png");
		DWORD rb25 = Draw::GetSharedImage(isNew, variant, ba25);
		if (rb25) g_mgImgSprayA25 = Draw::SharedImageRefToImage(rb25);
		// 花瓣染色图（python 生成：原花瓣乘色）+ 原图（恢复用）
		Draw::PString po = Draw::ToString("reanim\\Marigold_petals.png");
		DWORD ro = Draw::GetSharedImage(isNew, variant, po);
		if (ro) g_mgImgPetalsOrig = Draw::SharedImageRefToImage(ro);
		Draw::PString pb = Draw::ToString("images\\Marigold_petals_blue.png");
		DWORD rb2 = Draw::GetSharedImage(isNew, variant, pb);
		if (rb2) g_mgImgPetalsBlue = Draw::SharedImageRefToImage(rb2);
		Draw::PString py = Draw::ToString("images\\Marigold_petals_yellow.png");
		DWORD ry = Draw::GetSharedImage(isNew, variant, py);
		if (ry) g_mgImgPetalsYellow = Draw::SharedImageRefToImage(ry);
		Draw::PString pg = Draw::ToString("images\\Marigold_petals_green.png");
		DWORD rg = Draw::GetSharedImage(isNew, variant, pg);
		if (rg) g_mgImgPetalsGreen = Draw::SharedImageRefToImage(rg);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_mgImagesLoaded = false;
	}
}

// 绘制单个产出物图标（含渐隐：下次产前 1s 按档位切换 alpha 图）
static void MgDrawItemIcon(int itemIdx, DWORD g, int playingTime)
{
	(void)playingTime;
	int cx = 0, cy = 0;
	if (!MgItemCenter(itemIdx, &cx, &cy))
		return;
	int type = g_mgItems[itemIdx].type;
	int fade = MgItemFadeLevel(itemIdx);
	if (fade < 0)
		return;   // 完全淡出，不绘制
	int w = (type == 2) ? 68 : (type == 3) ? 72 : 80;
	int h = w;
	// 按渐隐档位选图（a50 半透明 / a25 更透明）
	DWORD img;
	if (fade == 0)
		img = (type == 0) ? g_mgImgFertilizer : (type == 1) ? g_mgImgWater
			: (type == 2) ? g_mgImgPhono : g_mgImgSpray;
	else if (fade == 1)
		img = (type == 0) ? g_mgImgFertA50 : (type == 1) ? g_mgImgWaterA50
			: (type == 2) ? g_mgImgPhonoA50 : g_mgImgSprayA50;
	else
		img = (type == 0) ? g_mgImgFertA25 : (type == 1) ? g_mgImgWaterA25
			: (type == 2) ? g_mgImgPhonoA25 : g_mgImgSprayA25;
	if (img)
		Draw::DrawImage(cx - w / 2, cy - h / 2, img, g);
	if (g_mgSelected == itemIdx)
	{
		Draw::SetColor(255, 255, 0, g);
		Draw::DrawRect(cx - 24, cy - 24, 48, 48, g);   // 选中黄圈
	}
}

// 绘制金盏花 UI（onDrawUITop 调用）：悬浮产出物 / 选中跟随 / 杀虫剂区域 / 留声机加成
static void DrawMarigoldUI()
{
	DWORD g = (g_expPouchGStore != 0) ? MemSafeRead<DWORD>(g_expPouchGStore) : 0;
	if (!g || !ExpPouchGraphicsValid(g))
		return;
	__try
	{
		int pvzBase = MemSafeRead<int>(0x6A9EC0);
		if (pvzBase < 0x400000)
			return;
		int boardAddr = MemSafeRead<int>(pvzBase + 0x768);
		if (!boardAddr)
			return;
		int gameMode = MemSafeRead<int>(pvzBase + 0x7F8);
		if (gameMode == 0x2B || gameMode == 0x32)
			return;   // 禅境花园/智慧树不绘制
		int playingTime = MemSafeRead<int>(boardAddr + 0x5568);

		// 1) 悬浮产出物
		for (int i = 0; i < g_mgItemCount; i++)
		{
			if (g_mgSelected == i)
				continue;   // 选中的画在鼠标处
			MgDrawItemIcon(i, g, playingTime);
		}

		// 2) 选中：图标跟随鼠标（★用户要求：移除技能文字/杀虫剂悬停格子高亮/留声机黄框）
		if (g_mgSelected >= 0 && g_mgSelected < g_mgItemCount)
		{
			int type = g_mgItems[g_mgSelected].type;
			int w = (type == 2) ? 68 : (type == 3) ? 72 : 80;
			int h = w;
			if (g_expPouchMouseX >= 0 && g_expPouchMouseY >= 0)
			{
				DWORD img = (type == 0) ? g_mgImgFertilizer : (type == 1) ? g_mgImgWater
					: (type == 2) ? g_mgImgPhono : g_mgImgSpray;
				if (img)
					Draw::DrawImage(g_expPouchMouseX - w / 2, g_expPouchMouseY - h / 2, img, g);
			}
		}

		// ★ 杀虫剂区域效果指示全部移除（用户要求）：绿框/静止图标/剩余时间都不画，
		//   区域效果由循环播放的 Spray 动画（reanim）本身指示
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 右键切换形态（0白→1蓝→2黄→3绿 循环，受等阶上限约束）+ 特效46（看星星）
static void MgCycleForm(DWORD plant, DWORD boardAddr)
{
	(void)boardAddr;
	MgPlantRec* r = MgFindPlantRec(plant);
	if (!r)
		return;
	int exp = 0;
	auto it = g_plantExperience.find(plant);
	if (it != g_plantExperience.end())
		exp = it->second;
	int tier = GetPlantTier((int)SeedType::Marigold, exp);
	if (tier > 3) tier = 3;
	if (tier < 0) tier = 0;
	int newForm = (r->form + 1) % (tier + 1);
	if (newForm == r->form)
		return;   // 0阶只能白色：不切、不播特效
	r->form = newForm;
	// 特效46（看星星特效）——CreateEffect = CreateParticleSystem(x, y, 0x618A0, type)
	__try
	{
		int px = MemSafeRead<int>(plant + 0x8);
		int py = MemSafeRead<int>(plant + 0xC);
		int pw = MemSafeRead<int>(plant + 0x10);
		int ph = MemSafeRead<int>(plant + 0x14);
		if (pw > 0 && pw <= 400 && ph > 0 && ph <= 400)
			Creator::CreateEffect((EffectType::EffectType)0x46, (float)(px + pw / 2), (float)(py + ph / 2));
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 植物移除清理（onPlantRemove 调用）
static void MgCleanupPlant(DWORD plant)
{
	if (!plant)
		return;
	for (int i = g_mgItemCount - 1; i >= 0; i--)
	{
		if (g_mgItems[i].plant != plant)
			continue;
		if (g_mgSelected == i)
			g_mgSelected = -1;
		g_mgItems[i] = g_mgItems[g_mgItemCount - 1];
		g_mgItemCount--;
		if (g_mgSelected == g_mgItemCount)
			g_mgSelected = i;   // 原末尾项（可能是选中项）被移到 i
	}
	for (int i = g_mgBoostCount - 1; i >= 0; i--)
	{
		if (g_mgBoosts[i].plant != plant)
			continue;
		g_mgBoosts[i] = g_mgBoosts[g_mgBoostCount - 1];
		g_mgBoostCount--;
	}
	for (int i = g_mgSprayCount - 1; i >= 0; i--)
	{
		if (g_mgSprays[i].source != plant)
			continue;
		g_mgSprays[i] = g_mgSprays[g_mgSprayCount - 1];
		g_mgSprayCount--;
	}
	for (int i = 0; i < g_mgPlantCount; i++)
	{
		if (g_mgPlants[i].plant != plant)
			continue;
		g_mgPlants[i] = g_mgPlants[g_mgPlantCount - 1];
		g_mgPlantCount--;
		break;
	}
}

// 新关卡全量重置（onNewGame 调用）
static void MgResetAll()
{
	g_mgPlantCount = 0;
	g_mgItemCount = 0;
	g_mgSelected = -1;
	g_mgSprayCount = 0;
	g_mgBoostCount = 0;
	g_mgItemSerial = 0;
	g_mgPrevRB = 0;
	g_mgFxCount = 0;   // 使用效果动画记录清空（reanim 对象随关卡销毁，无需逐个 Die）
}

// 金盏花每帧轮询内部实现（__try 外壳在 UpdateMarigoldFrame，C2712）
static void UpdateMarigoldFrameInner(DWORD boardAddress)
{
	PVZ::Board board(boardAddress);
	if (!board.GetBaseAddress())
		return;
	int playingTime = board.PlayingTime;
	auto plants = board.GetAllPlants();

	// --- 0. 收集金盏花：产出间隔覆盖 + 咖啡豆唤醒检测 + 形态染色 ---
	for (auto& p : plants)
	{
		if (p.Type != SeedType::Marigold || p.NotExist)
			continue;
		DWORD pa = p.GetBaseAddress();
		if (!pa)
			continue;

		// 可配置产出间隔（0=原版）
		if (g_mgProduceIntervalCs > 0)
			MemSafeWrite<int>(pa + 0x5C, g_mgProduceIntervalCs);

		// 咖啡豆唤醒检测：同格出现咖啡豆 → 解锁等阶（同保护伞）
		if (g_coffeeAwakenedPlants.count(pa) == 0)
		{
			int row = (int)p.Row, col = (int)p.Column;
			for (auto& cb : plants)
			{
				if (cb.Type != SeedType::CoffeeBean || cb.NotExist)
					continue;
				if ((int)cb.Row != row || (int)cb.Column != col)
					continue;
				DWORD cbAddr = cb.GetBaseAddress();
				if (!cbAddr)
					continue;
				g_coffeeAwakenedPlants.insert(pa);
				InitPlantExperience(pa);   // 解锁：补建经验条目（0经验起步）
				break;
			}
		}

		// 等阶 → 形态上限（未唤醒 exp=0 → tier 0）
		int exp = 0;
		auto eit = g_plantExperience.find(pa);
		if (eit != g_plantExperience.end())
			exp = eit->second;
		int tier = GetPlantTier((int)SeedType::Marigold, exp);
		if (tier > 3) tier = 3;
		if (tier < 0) tier = 0;

		// 登记 + 形态收敛到等阶
		MgPlantRec* r = MgFindPlantRec(pa);
		if (!r)
		{
			MgSetForm(pa, 0);
			r = MgFindPlantRec(pa);
		}
		if (!r)
			continue;
		if (r->form > tier)
			r->form = tier;

		// 花瓣染色：form 或 reanim 地址变化才 SetImageOverride（替换花瓣轨道图片）。
		// ★ reanim 可能因状态切换重建（地址变化），重建后需重新替换，故记录 lastReanim
		{
			PVZ::Plant pl(pa);
			PVZ::Animation anim = pl.GetAnimationPart1();
			DWORD animAddr = anim.GetBaseAddress();
			if (r->lastTint != r->form || r->lastReanim != animAddr)
			{
				r->lastTint = r->form;
				r->lastReanim = animAddr;
				MgApplyPetalsTint(pa, r->form);
			}
		}
	}

	// --- 1. 清理：产出物所属金盏花已消失 / 寿命到期 / 加成到期 / 杀虫剂到期 ---
	// ★ 寿命到期（物品自身剩余寿命 <= 25 厘秒）→ 真正销毁物品。
	//   用物品自带计时（spawnCs/lifeCs）而非实时倒计时：玩家拾起再取消后也能准时销毁。
	//   正在拖拽使用的选中项豁免（拖完放下后下一帧即判定）。
	for (int i = g_mgItemCount - 1; i >= 0; i--)
	{
		DWORD pp = g_mgItems[i].plant;
		bool gone = (MemSafeRead<BYTE>(pp + 0x141)
			|| MemSafeRead<int>(pp + 0x24) != (int)SeedType::Marigold);
		if (!gone && g_mgSelected != i)
		{
			if (MgItemRemainCs(i) <= 25)
				gone = true;
		}
		if (gone)
		{
			if (g_mgSelected == i)
				g_mgSelected = -1;
			g_mgItems[i] = g_mgItems[g_mgItemCount - 1];
			g_mgItemCount--;
			// swap-remove：原末尾项（可能是选中项）被移到 i，修正 g_mgSelected
			if (g_mgSelected == g_mgItemCount)
				g_mgSelected = i;
		}
	}
	for (int i = g_mgBoostCount - 1; i >= 0; i--)
	{
		if (playingTime >= g_mgBoosts[i].endCs)
		{
			g_mgBoosts[i] = g_mgBoosts[g_mgBoostCount - 1];
			g_mgBoostCount--;
		}
	}
	for (int i = g_mgSprayCount - 1; i >= 0; i--)
	{
		if (playingTime - g_mgSprays[i].startCs >= g_mgSprayDurationCs)
		{
			g_mgSprays[i] = g_mgSprays[g_mgSprayCount - 1];
			g_mgSprayCount--;
		}
	}
	// (d) 使用效果动画到期销毁（水壶/肥料/留声机/杀虫剂 reanim）
	for (int i = g_mgFxCount - 1; i >= 0; i--)
	{
		if (playingTime < g_mgFxAnims[i].endCs)
			continue;
		MgKillReanim(g_mgFxAnims[i].addr);
		g_mgFxAnims[i] = g_mgFxAnims[g_mgFxCount - 1];
		g_mgFxCount--;
	}

	// --- 2. 右键切换形态（GetAsyncKeyState 沿检测，同粒子预览器；暂停中不处理）---
	int rb = (GetAsyncKeyState(VK_RBUTTON) & 0x8000) ? 1 : 0;
	if (rb && !g_mgPrevRB && !MemSafeRead<BYTE>(boardAddress + 0x164))
	{
		if (g_expPouchMouseX >= 0 && g_expPouchMouseY >= 0)
		{
			int col = -1, row = -1;
			if (ExpPouchPixelToGrid(boardAddress, g_expPouchMouseX, g_expPouchMouseY, &col, &row))
			{
				DWORD plant = ExpPouchFindPlantAt(boardAddress, row, col);
				if (plant && MemSafeRead<int>(plant + 0x24) == (int)SeedType::Marigold)
				{
					MgCycleForm(plant, boardAddress);
				}
				else if (plant && MemSafeRead<int>(plant + 0x24) == (int)SeedType::SplitPea)
				{
					auto expIt = g_plantExperience.find(plant);
					if (expIt != g_plantExperience.end())
					{
						int tier = GetPlantTier((int)SeedType::SplitPea, expIt->second);
						if (tier >= 5)
							SplitPeaCycleForm(plant, boardAddress);
					}
				}
				else if (plant && MemSafeRead<int>(plant + 0x24) == (int)SeedType::Melonpult)
				{
					// 西瓜投手卡3阶：右键打开升级路线选择窗口（未达标时内部直接忽略）
					MelonOnRightClick(plant, boardAddress);
				}
				else if (plant && MemSafeRead<int>(plant + 0x24) == (int)SeedType::Garlic)
				{
					// 大蒜2阶：右键切换换行方向（受关卡行约束时该行不可切换）
					GarlicOnRightClick(plant, boardAddress);
				}
				else
				{
					g_mgSelected = -1;   // 右键点别处：取消产出物选中
				}
			}
		}
	}
	g_mgPrevRB = rb;

	// --- 3. 杀虫剂区域伤害 tick（每秒 50 真伤，有来源=金盏花）---
	if (g_mgSprayCount > 0)
	{
		auto zombies = board.GetAllZombies();
		for (int s = 0; s < g_mgSprayCount; s++)
		{
			int elapsed = playingTime - g_mgSprays[s].startCs;
			if (elapsed < 0)
				continue;
			int tickNow = elapsed / 100;
			if (tickNow <= g_mgSprays[s].ticks)
				continue;
			int dmgTicks = tickNow - g_mgSprays[s].ticks;
			g_mgSprays[s].ticks = tickNow;
			int cellX = 25 + g_mgSprays[s].col * 80;
			DWORD src = g_mgSprays[s].source;
			bool srcAlive = src && !MemSafeRead<BYTE>(src + 0x141);
			for (auto& z : zombies)
			{
				if (z.NotExist)
					continue;
				if ((int)z.Row != g_mgSprays[s].row)
					continue;
				float zx = z.X;
				if (zx < cellX - 15 || zx > cellX + 95)
					continue;
				DWORD za = z.GetBaseAddress();
				if (!za)
					continue;
				if (MemSafeRead<BYTE>(za + 0xB9))
					continue;   // 已吹飞
				// 有来源伤害：写入僵尸伤害来源字段（+0x148），击杀经验归金盏花
				if (srcAlive)
					MemSafeWrite<int>(za + 0x148, (int)src);
				for (int t = 0; t < dmgTicks; t++)
				{
					PVZ::Zombie zz(za);
					if (zz.NotExist)
						break;
					zz.HitBody(g_mgSprayDps, PVZ::DAMAGEF_NONE);   // 真伤：无视护甲
				}
			}
		}
	}
}

// 金盏花每帧轮询入口（onGameObjectsUpdate 调用；__try 外壳防地址回收等异常）
static void UpdateMarigoldFrame(DWORD boardAddress)
{
	__try
	{
		UpdateMarigoldFrameInner(boardAddress);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ==================== 保护伞（UmbrellaLeaf）等阶机制 ====================
// 保护伞默认无等阶/经验/文字，种上咖啡豆后解锁（见"咖啡豆唤醒解锁等阶系统"）。
// 解锁后等阶（配置特征三阶即满阶，plant_tier.ini 37 行）：
//   0阶: 同原版（挡篮球/蹦极）
//   1阶: 打在保护伞上的僵尸豌豆(ZombiePea)被原样反弹(XSpeed取反)，伞不受伤害
//   2阶: 3×3范围内巨人投掷的飞行小鬼(IMP_FLYING)被弹飞
//   3阶: 1×3范围内起跳的撑杆/海豚/撑杆司令(类型3同撑杆)被弹飞
// 全部零 hook：onGameObjectsUpdate 每帧纯内存轮询（同撑杆司令模式）。
// 弹飞手法与 S4修猫"保护伞弹小鬼"字节级一致：
//   Blowaway(+0xB9)=1 + [z+0x120]=5.0f + VelX(+0x34)*=-2 + 伞动画/音效。

// 播放保护伞弹开表现（S4修猫同款）：SetAnimation(0x45FD90) + 状态0x29 + 图层刷新 + 音效44
// ★ 两段 __asm 调用均被 pushad/popad 包裹，栈平衡由 POPAD 兜底（与 TriplePlayUltSound 同套路）
static void UmbrellaPlayBounceFX(DWORD plantAddr)
{
	// 动画: Plant::SetAnimation(eax=plant, [esp]=动画名串@0x669058, [esp+4]=3, [esp+8]=12.0f)
	__asm {
		pushad
		push 0x41400000          ; (float)12.0 的位模式
		xor ecx, ecx
		push 3
		push 0x669058
		mov eax, plantAddr
		mov ebx, 0x45FD90
		call ebx
		popad
	}
	// 状态 → UMBRELLA_LEAF_SHRINK(0x29)，并按原式刷新图层 row*10000+0x4CE78
	MemSafeWrite<int>(plantAddr + 0x3C, 0x29);
	int row = MemSafeRead<int>(plantAddr + 0x1C);
	MemSafeWrite<int>(plantAddr + 0x20, row * 10000 + 0x4CE78);
	// 音效: SexyApp::PlaySound(44)（ecx=[0x6A9EC0]，stdcall ret 4）
	__asm {
		pushad
		mov ecx, 0x6A9EC0
		mov ecx, [ecx]
		push 44
		mov ebx, 0x4560C0
		call ebx
		popad
	}
}

// 保护伞每帧轮询内部实现（含局部对象，__try 必须放外层包装，C2712）
static void UpdateUmbrellaFrameInner(DWORD boardAddress)
{
	PVZ::Board board(boardAddress);
	if (!board.GetBaseAddress())
		return;
	auto plants = board.GetAllPlants();

	// --- 0. 咖啡豆唤醒检测：同格出现咖啡豆植物 → 解锁该保护伞 ---
	for (auto& cb : plants)
	{
		if (cb.Type != SeedType::CoffeeBean || cb.NotExist)
			continue;
		int row = (int)cb.Row, col = (int)cb.Column;
		for (auto& q : plants)
		{
			if (q.Type != SeedType::UmbrellaLeaf || q.NotExist)
				continue;
			if ((int)q.Row != row || (int)q.Column != col)
				continue;
			DWORD qa = q.GetBaseAddress();
			if (qa == 0 || g_coffeeAwakenedPlants.count(qa))
				continue;
			g_coffeeAwakenedPlants.insert(qa);
			InitPlantExperience(qa);   // 解锁：补建经验条目（0经验起步）
		}
	}

	// --- 1. 收集已解锁的1阶及以上保护伞 ---
	struct UmbInfo { DWORD addr; int tier; int row; int x; int w; };
	std::vector<UmbInfo> umbs;
	for (auto& p : plants)
	{
		if (p.Type != SeedType::UmbrellaLeaf || p.NotExist)
			continue;
		DWORD pa = p.GetBaseAddress();
		if (pa == 0 || g_coffeeAwakenedPlants.count(pa) == 0)
			continue;
		int exp = 0;
		auto it = g_plantExperience.find(pa);
		if (it != g_plantExperience.end())
			exp = it->second;
		int tier = GetPlantTier((int)SeedType::UmbrellaLeaf, exp);
		if (tier <= 0)
			continue;   // 0阶同原版
		UmbInfo u;
		u.addr = pa;
		u.tier = tier;
		u.row = MemSafeRead<int>(pa + 0x1C);
		u.x = MemSafeRead<int>(pa + 0x8);    // ImageX（与僵尸+0x8同坐标系）
		u.w = MemSafeRead<int>(pa + 0x10);   // Width
		umbs.push_back(u);
	}
	if (umbs.empty())
		return;

	// --- 2. T2/T3：弹飞投掷小鬼 / 起跳的撑杆·海豚·撑杆司令 ---
	auto zombies = board.GetAllZombies();
	for (auto& z : zombies)
	{
		if (z.NotExist)
			continue;
		DWORD za = z.GetBaseAddress();
		if (za == 0)
			continue;
		if (MemSafeRead<BYTE>(za + 0xB9))
			continue;   // 已被吹飞（含本弹飞后的持续帧，天然去重）
		int ztype = MemSafeRead<int>(za + 0x24);
		int zstate = MemSafeRead<int>(za + 0x28);
		// T2: 巨人投掷的小鬼（飞行中）；T3: 起跳中的撑杆(类型3含司令)/海豚
		bool thrownImp = (ztype == (int)ZombieType::Imp && zstate == (int)ZombieState::IMP_FLYING);
		bool jumper = ((ztype == (int)ZombieType::PoleVaultingZombie && zstate == (int)ZombieState::POLE_VALUTING_JUMPPING)
					|| (ztype == (int)ZombieType::DolphinRiderZombie && zstate == (int)ZombieState::DOPHIN_JUMP));
		if (!thrownImp && !jumper)
			continue;
		int zrow = MemSafeRead<int>(za + 0x1C);
		if (zrow < 0 || zrow > 5)
			continue;
		int zx = MemSafeRead<int>(za + 0x8);

		for (auto& u : umbs)
		{
			if (thrownImp)
			{
				if (u.tier < 2)
					continue;
				if (zrow < u.row - 1 || zrow > u.row + 1)
					continue;   // 3×3：行±1
				if (zx < u.x - 120 || zx > u.x + 150)
					continue;   // 列向像素范围（S4修猫原值，≈3列）
			}
			else
			{
				if (u.tier < 3)
					continue;
				if (zrow != u.row)
					continue;   // 1×3：同行
				if (zx < u.x - 120 || zx > u.x + 120)
					continue;
			}
			// 弹飞（S4修猫同款）
			MemSafeWrite<BYTE>(za + 0xB9, 1);          // Blowaway 起飞
			MemSafeWrite<float>(za + 0x120, 5.0f);
			float vx = MemSafeRead<float>(za + 0x34); // VelX
			MemSafeWrite<float>(za + 0x34, -2.0f * vx);
			UmbrellaPlayBounceFX(u.addr);
			break;
		}
	}

	// --- 3. T1：僵尸豌豆原样反弹（XSpeed 取反飞回僵尸侧，伞不受伤害） ---
	auto projectiles = board.GetAllProjectile();
	for (auto& proj : projectiles)
	{
		if (proj.NotExist)
			continue;
		if (proj.Type != ProjectileType::ZombiePea)
			continue;
		float vx = proj.XSpeed;
		if (vx >= 0.0f)
			continue;   // 向右 = 已反弹/魅惑僵尸方的子弹，不处理
		int prow = (int)proj.Row;
		if (prow < 0 || prow > 5)
			continue;
		float px = proj.X;
		for (auto& u : umbs)
		{
			if (u.row != prow)
				continue;
			if (px > u.x + u.w)
				continue;   // 还没到伞（以贴图右缘为反弹点，提前于原生碰撞）
			if (px < u.x - 20)
				continue;   // 已越过（防御，正常每帧扫描不会漏）
			proj.XSpeed = -vx;
			UmbrellaPlayBounceFX(u.addr);
			break;
		}
	}
}

// 保护伞每帧轮询入口（__try 外壳，防地址回收等异常）
static void UpdateUmbrellaFrame(DWORD boardAddress)
{
	__try
	{
		UpdateUmbrellaFrameInner(boardAddress);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ===== 强制钱币计数器常驻（已停用 / DEPRECATED）=====
// 历史：经验文字颜色异常时，靠强制 DrawUICoinBank 每帧执行来"顺带"刷新
// DDraw/Graphics 状态，属于不知道原理的绕路修复（还会强制显示钱币数）。
// 2026-10-20 起经验文字改为 NativeDrawExpGlyphs（游戏自带字形图 + DrawImage），
// 颜色/字号不再依赖任何共享 DC 状态，本补丁不再调用。
// 保留函数体仅供回溯；不要重新启用。
static bool g_forceCoinBankInstalled = false;
void InstallForceCoinBank()
{
	BYTE nop6[6] = { 0x90,0x90,0x90,0x90,0x90,0x90 };
	BYTE nop2[2] = { 0x90,0x90 };
	BYTE cur[6];

	// 0x41A2CC: jz (74 0D)
	PVZ::Memory::ReadArray<BYTE>(0x41A2CC, cur, 2);
	if (cur[0] == 0x74)
		PVZ::Memory::WriteArray<BYTE>(0x41A2CC, nop2, 2);

	// 0x41A2D5: jz (0F 84 3D 01 00 00)
	PVZ::Memory::ReadArray<BYTE>(0x41A2D5, cur, 6);
	if (cur[0] == 0x0F && cur[1] == 0x84)
		PVZ::Memory::WriteArray<BYTE>(0x41A2D5, nop6, 6);

	// 0x41A2E2: jle (0F 8E 30 01 00 00)
	PVZ::Memory::ReadArray<BYTE>(0x41A2E2, cur, 6);
	if (cur[0] == 0x0F && cur[1] == 0x8E)
		PVZ::Memory::WriteArray<BYTE>(0x41A2E2, nop6, 6);
}

// ==================== 究极大喷菇（UltFume）：大喷菇(Fumeshroom=10) 改造 ====================
//
// 【规格】
//   · 攻击范围：全行
//   · 每 0.5 秒对范围内所有僵尸：100 伤害 + 减速 + 累计 10 点冻结值
//   · 僵尸生命值 < 50% 时，每次攻击 1% 概率魅惑；魅惑成功 → 该位置 3×3 爆炸（360 伤害）
//   · 冻结值：上限 100，满值 → 寒冰菇式冻结 → 清零 → 上限 +100（最高 400）
//
// 【逆向结论】（反汇编见根目录 dis_plant_region.txt / dis_shooting.txt）
//   1) Plant::UpdateShooter 0x45F8A0：
//        [plant+0x58] 每 tick -1，<=0 时进入开火分支；重装载值 = [plant+0x5C] - rand(0..14)。
//        默认分支（含大喷菇）调用 Plant::FindTargetAndFire 0x45EF10。
//      → 我们每帧直接写 [plant+0x58] 精确接管节奏：写 1 = 下一 tick 必定开火，
//        写 9999 = 保持等待。这样绕开 rand 抖动，也绕开飞升版攻速系统对大喷菇的缩放。
//   2) Plant::FindTargetAndFire 0x45EF10：
//        先 Plant::FindTargetZombie 0x4675C0 索敌（原版按攻击矩形，只覆盖身前约 3.5 格，
//        找不到目标就不开火）；命中后播 anim_shoot 并置 [plant+0x90] = 50。
//   3) Plant::UpdateShooting 0x464820：
//        [plant+0x90]（ShootingCountdown）递减；==1 时走默认分支 → Plant::Fire(plant,0,row,0)；
//        ==0 时播收招动画。即"开火时刻 = 触发后第 48 tick"，第 49 tick 回到待机（0x90=0）。
//   4) Plant::Fire 0x466E00：
//        type==0x0A（大喷菇）不产生子弹，直接 Plant::DoRowAreaDamage(plant, 2)，
//        对攻击矩形内僵尸造成 20 伤害（0x45ED00 内 push 0x14 + call 0x5317C0）。
//
// 【两个 hook（都在入口处 cmp type,0x0A，非大喷菇 100% 走原路径）】
//   A) 0x4675C0 Plant::FindTargetZombie 入口（6 字节：55 8B EC 83 E4 F8）
//      → 大喷菇改由 UltFumeFindTarget 按"全行"索敌，其余植物原样进入。
//   B) 0x466E15 Plant::Fire 内 `jne 0x466E82 / push 2 / push ebp`（5 字节）
//      → 大喷菇改走 UltFumeFire 做全行结算，然后跳 epilogue 0x46754C 返回 0（无子弹）；
//        其它植物跳 0x466E82 继续原流程。
// ============================================================================

#define ULF_SLOTS     2048   // 状态槽位数（僵尸/植物 DataArray 上限 1024，取 2 倍留余量）
#define ULF_MAX_HITS  512    // 单次攻击最多结算的僵尸数
#define ULF_HOLD_CD   9999   // 写进 [plant+0x58] 的"保持等待"值

// 冻结值状态（按僵尸 Id 校验槽位，僵尸内存池复用时自动重置，零分配、hook 帧内安全）
static int   g_ulfZombieId[ULF_SLOTS];
static int   g_ulfFreezeVal[ULF_SLOTS];
static int   g_ulfFreezeCap[ULF_SLOTS];
// 开火节奏状态（同理按植物 Id 校验）
static int   g_ulfPlantId[ULF_SLOTS];
static int   g_ulfPlantLastFire[ULF_SLOTS];

// hook trampoline 与 C++ 之间的传参（静态变量，不压栈不分配）
static DWORD g_ulfTmpPlant  = 0;
static int   g_ulfTargetRet = 0;

// 一次攻击的目标快照
static DWORD g_ulfHitAddr[ULF_MAX_HITS];
static int   g_ulfHitId[ULF_MAX_HITS];
static int   g_ulfHitCount = 0;

static bool  g_ulfHooksInstalled = false;

// ---- 自检计数器（ULF_DEBUG=1 时每秒落盘一行，用于"看起来没生效"的一线排障）----
// 只写 D:\pvz_ulf_debug.txt，用纯 Win32（CreateFileA/WriteFile），不用 CRT（铁律）
static int   g_ulfDbgFrame    = 0;   // 轮询被执行了多少帧
static int   g_ulfDbgPlants   = 0;   // 最近一帧看到的大喷菇株数
static int   g_ulfDbgTrigger  = 0;   // 累计"发出开火指令"次数
static int   g_ulfDbgFire     = 0;   // UltFumeFire（hook B）被调用次数
static int   g_ulfDbgHits     = 0;   // 累计结算到的僵尸次数
static int   g_ulfDbgTarget   = 0;   // UltFumeFindTarget（hook A）被调用次数
static int   g_ulfDbgFallback = 0;   // 自研索敌落空、回退原版索敌的次数
static int   g_ulfDbgErr      = 0;   // 轮询内被 __try 吞掉的异常次数
static int   g_ulfHookAState  = 0;   // 0未安装 1已安装 -1字节不符 -2trampoline分配失败
static int   g_ulfHookBState  = 0;
static int   g_ulfInstallTries = 0;

// 极简 itoa（不碰 CRT）
static void UlfItoa(int v, char* out)
{
	char tmp[16];
	int n = 0;
	int neg = 0;
	if (v < 0) { neg = 1; v = (v == -2147483647 - 1) ? 2147483647 : -v; }
	if (v == 0) tmp[n++] = '0';
	while (v > 0 && n < 15) { tmp[n++] = (char)('0' + (v % 10)); v /= 10; }
	int p = 0;
	if (neg) out[p++] = '-';
	while (n > 0) out[p++] = tmp[--n];
	out[p] = 0;
}

// 自检日志：覆盖写 D:\pvz_ulf_debug.txt（每次都是完整一行，不需要 tail）
static void UlfDebugFlush(const char* tag)
{
	if (!g_ulfDebug) return;
	char buf[512];
	int p = 0;
#define ULF_PUTS(s) do { const char* _s = (s); while (*_s && p < 470) buf[p++] = *_s++; } while (0)
#define ULF_PUTN(v) do { char _t[16]; UlfItoa((int)(v), _t); const char* _s2 = _t; while (*_s2 && p < 470) buf[p++] = *_s2++; } while (0)
	ULF_PUTS("[ULTFUME build 20260829-v3] ");
	ULF_PUTS(tag);
	ULF_PUTS(" enabled="); ULF_PUTN(g_ulfEnabled);
	ULF_PUTS(" hookA=");   ULF_PUTN(g_ulfHookAState);
	ULF_PUTS(" hookB=");   ULF_PUTN(g_ulfHookBState);
	ULF_PUTS(" tries=");   ULF_PUTN(g_ulfInstallTries);
	ULF_PUTS(" frame=");   ULF_PUTN(g_ulfDbgFrame);
	ULF_PUTS(" plants=");  ULF_PUTN(g_ulfDbgPlants);
	ULF_PUTS(" target=");  ULF_PUTN(g_ulfDbgTarget);
	ULF_PUTS(" fallback=");ULF_PUTN(g_ulfDbgFallback);
	ULF_PUTS(" trigger="); ULF_PUTN(g_ulfDbgTrigger);
	ULF_PUTS(" fire=");    ULF_PUTN(g_ulfDbgFire);
	ULF_PUTS(" hits=");    ULF_PUTN(g_ulfDbgHits);
	ULF_PUTS(" err=");     ULF_PUTN(g_ulfDbgErr);
	ULF_PUTS(" interval=");ULF_PUTN(g_ulfIntervalCs);
	ULF_PUTS(" dmg=");     ULF_PUTN(g_ulfDamage);
	ULF_PUTS("\r\n");
#undef ULF_PUTS
#undef ULF_PUTN
	buf[p] = 0;

	HANDLE h = CreateFileA("D:\\pvz_ulf_debug.txt", GENERIC_WRITE, FILE_SHARE_READ,
		NULL, OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
	if (h != INVALID_HANDLE_VALUE)
	{
		SetFilePointer(h, 0, NULL, FILE_BEGIN);
		DWORD written = 0;
		WriteFile(h, buf, (DWORD)p, &written, NULL);
		CloseHandle(h);
	}
}

static int UlfSlot(DWORD id)
{
	int s = (int)(id & 0xFFFF);
	return (s >= 0 && s < ULF_SLOTS) ? s : -1;
}

// 新游戏 / 换关：清空全部状态
static void UltFumeResetAll()
{
	for (int i = 0; i < ULF_SLOTS; i++)
	{
		g_ulfZombieId[i] = 0;
		g_ulfFreezeVal[i] = 0;
		g_ulfFreezeCap[i] = 0;
		g_ulfPlantId[i] = 0;
		g_ulfPlantLastFire[i] = -1000000;   // 负值 → 换关后立刻可开火，不受 PlayingTime 归零影响
	}
	g_ulfHitCount = 0;
}

// 僵尸是否可作为攻击目标：同行 / 未移除 / 未被魅惑 / 非垂死
// （对齐原版 DoRowAreaDamage 0x45ED00 的过滤子集：NotExist、Row、EffectedBy、State）
static bool UlfTargetable(DWORD zombieAddr, int row)
{
	if (zombieAddr < 0x10000) return false;
	if (MemSafeRead<BYTE>(zombieAddr + 0xEC)) return false;      // NotExist
	if (MemSafeRead<int>(zombieAddr + 0x1C) != row) return false; // Row
	if (MemSafeRead<BYTE>(zombieAddr + 0xB8)) return false;       // Hypnotized
	int st = MemSafeRead<int>(zombieAddr + 0x28);                 // State
	if (st == 1 || st == 2 || st == 3) return false;                          // 垂死三态
	return true;
}

// 当前生命值是否低于最大生命值的 percent%
static bool UlfHpBelow(PVZ::Zombie& z, int percent)
{
	int cur, max;
	if (g_ulfCharmTotalHp)
	{
		cur = z.BodyHealth + z.HelmHealth + z.ShieldHealth + z.FlyingHealth;
		max = z.BodyMaxHealth + z.HelmMaxHealth + z.ShieldMaxHealth + z.FlyingMaxHealth;
	}
	else
	{
		cur = z.BodyHealth;
		max = z.BodyMaxHealth;
	}
	if (max <= 0) return false;
	return (cur * 100) < (max * percent);
}

// 播放游戏音效（与金盏花 MgPlayUseSound 同款：0x515020，eax=音效ID, ecx=AudioPlayer, 栈=音量）
static void UlfPlaySound(int id)
{
	__asm {
		pushad
		mov ecx, 0x6A9EC0
		mov ecx, dword ptr [ecx]
		mov ecx, dword ptr [ecx + 0x784]
		mov eax, id
		push 0x3F800000
		mov ebx, 0x515020
		call ebx
		popad
	}
}

// 魅惑成功后的 3×3 爆炸：中心点 (row, cx)，排除刚被魅惑的僵尸本身（它已是友军）
static void UlfExplode(DWORD boardAddr, int row, float cx, DWORD srcAddr)
{
	float cy = 0.0f;
	if (boardAddr)
		cy = (float)PVZ::Board(boardAddr).GridToYPixel(row, 0) + 60.0f;
	Creator::CreateEffect(EffectType::CHERRY_BOMB_EXPLODED, cx, cy);
	if (g_ulfBoomSound > 0)
		UlfPlaySound(g_ulfBoomSound);

	if (g_ulfBoomDamage <= 0 || !boardAddr) return;
	if (boardAddr < 0x10000 || !CrashIsReadable(boardAddr, 0x1000)) return;
	int   maxnum = MemSafeRead<int>(boardAddr + 0x94);
	DWORD zbase  = MemSafeRead<DWORD>(boardAddr + 0x90);
	if (maxnum <= 0 || maxnum > 1024) return;
	if (zbase < 0x10000 || !CrashIsReadable(zbase, 0x15C * 8)) return;

	for (int i = 0; i < maxnum; i++)
	{
		DWORD za = zbase + 0x15C * (DWORD)i;
		if (za == srcAddr) continue;          // 刚被魅惑的僵尸不吃自己的爆炸
		if (MemSafeRead<BYTE>(za + 0xEC)) continue;   // NotExist
		if (MemSafeRead<BYTE>(za + 0xB8)) continue;   // 不误伤友军
		int st = MemSafeRead<int>(za + 0x28);   // State
		if (st == 1 || st == 2 || st == 3) continue;        // 垂死三态不吃爆炸
		int zrow = MemSafeRead<int>(za + 0x1C);
		if (zrow < row - g_ulfBoomRowRange || zrow > row + g_ulfBoomRowRange) continue;
		float zx = MemSafeRead<float>(za + 0x2C);
		if (zx < cx - (float)g_ulfBoomXRange || zx > cx + (float)g_ulfBoomXRange) continue;
		PVZ::Zombie z(za);
		z.Hit(g_ulfBoomDamage, PVZ::DAMAGEF_NONE);
	}
}

// ================= Hook A：全行索敌（替换原版 ~3.5 格攻击矩形）=================
// 由 trampoline 调用；入参 g_ulfTmpPlant=植物地址，出参 g_ulfTargetRet=僵尸地址(0=无目标)
// ★ 两个入口都套 __try 外壳：它们由 trampoline 从游戏函数**中间**调用，
//   一旦内部抛异常（vector 分配失败/野指针读），异常会穿过游戏代码无人接管。
//   Impl 含 std::vector，与 __try 同函数会触发 MSVC C2712，故拆成外壳 + Inner。
static void UlfScanRow(DWORD boardAddr, int row, int px);   // 限界僵尸扫描（定义在下方）

static void UltFumeFindTargetImpl()
{
	g_ulfTargetRet = 0;
	g_ulfDbgTarget++;
	DWORD plantAddr = g_ulfTmpPlant;
	if (!g_ulfEnabled || plantAddr < 0x10000) { g_ulfDbgFallback++; return; }
	if (MemSafeRead<int>(plantAddr + 0x24) != (int)SeedType::Fumeshroom) return;
	int  row  = MemSafeRead<int>(plantAddr + 0x1C);
	int  px   = MemSafeRead<int>(plantAddr + 0x8);
	// ★ GameObject::GetBoard() = [this+4]；[this+0] 是 LawnApp（PVZ.h 478-486 行写明）。
	//   v2 用成 plantAddr+0 → 拿 LawnApp 当 Board 去 GetAllZombies()，读到的是
	//   LawnApp+0x90/0x94 的无关字段 → 索敌/结算全废（v3 症状：攻速变了但射程伤害都没变）。
	DWORD boardAddr = MemSafeRead<int>(plantAddr + 4);
	UlfScanRow(boardAddr, row, px);

	// 取最靠前（X 最小）的僵尸
	DWORD best = 0;
	float bestX = 1.0e9f;
	for (int i = 0; i < g_ulfHitCount; i++)
	{
		float zx = MemSafeRead<float>(g_ulfHitAddr[i] + 0x2C);
		if (zx < bestX) { bestX = zx; best = g_ulfHitAddr[i]; }
	}
	g_ulfTargetRet = (int)best;
	if (best == 0)
		g_ulfDbgFallback++;   // 自研索敌落空 → trampoline 会回退原版索敌
}

// 扫一行可命中僵尸，填进 g_ulfHitAddr/g_ulfHitId/g_ulfHitCount
// ★ 自己遍历僵尸 DataArray 并严格限界，不用框架 GetAllZombies()：
//   ①hook 帧内不做堆分配 ②S6 的 CE 代码也会调用 FindTargetZombie(0x4675C0)，传入的
//   植物若不是场上实体，[plant+4] 可能是垃圾 → 框架版按 [board+0x94] 无限扩容会崩；
//   这里先校验 Board/数组基址可读、数量 ≤1024，再手动步进（Zombie MemSize=0x15C）。
static void UlfScanRow(DWORD boardAddr, int row, int px)
{
	g_ulfHitCount = 0;
	if (boardAddr < 0x10000) return;
	if (!CrashIsReadable(boardAddr, 0x1000)) return;

	int   maxnum = MemSafeRead<int>(boardAddr + 0x94);   // 僵尸 DataArray 容量
	DWORD zbase  = MemSafeRead<DWORD>(boardAddr + 0x90); // 僵尸 DataArray 基址
	if (maxnum <= 0 || maxnum > 1024) return;
	if (zbase < 0x10000 || !CrashIsReadable(zbase, 0x15C * 8)) return;

	for (int i = 0; i < maxnum && g_ulfHitCount < ULF_MAX_HITS; i++)
	{
		DWORD za = zbase + 0x15C * (DWORD)i;
		if (!UlfTargetable(za, row)) continue;
		float zx = MemSafeRead<float>(za + 0x2C);
		if (g_ulfFrontOnly && zx < (float)px) continue;
		g_ulfHitAddr[g_ulfHitCount] = za;
		g_ulfHitId[g_ulfHitCount] = MemSafeRead<int>(za + 0x158);   // Zombie.Id
		g_ulfHitCount++;
	}
}

static void __cdecl UltFumeFindTarget()
{
	__try
	{
		UltFumeFindTargetImpl();
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_ulfTargetRet = 0;
		g_ulfDbgFallback++;
	}
}

// ================= Hook B：全行攻击结算 =================
// ★ 双出口：g_ulfFireRet = 1 表示已按自研逻辑结算（trampoline 跳过原版 DoRowAreaDamage）；
//           = 0 表示本模块没干成任何事（trampoline 落回原版 DoRowAreaDamage）。
//   绝不允许"跳过了原版又什么都没做"——那会让大喷菇 0 伤害且无声无息。
static int   g_ulfFireRet = 0;

static void UltFumeFireImpl(DWORD plantAddr)
{
	g_ulfFireRet = 0;
	if (!g_ulfEnabled || plantAddr < 0x10000) return;
	if (MemSafeRead<int>(plantAddr + 0x24) != (int)SeedType::Fumeshroom) return;
	int  row  = MemSafeRead<int>(plantAddr + 0x1C);
	int  px   = MemSafeRead<int>(plantAddr + 0x8);
	// ★ GameObject::GetBoard() = [this+4]；[this+0] 是 LawnApp（PVZ.h 478-486 行写明）。
	//   v2 用成 plantAddr+0 → 拿 LawnApp 当 Board 去 GetAllZombies()，读到的是
	//   LawnApp+0x90/0x94 的无关字段 → 索敌/结算全废（v3 症状：攻速变了但射程伤害都没变）。
	DWORD boardAddr = MemSafeRead<int>(plantAddr + 4);
	UlfScanRow(boardAddr, row, px);
	g_ulfDbgFire++;
	if (g_ulfHitCount <= 0) return;   // 没目标 → 交还原版（原版此时也不会造成伤害）
	g_ulfDbgHits += g_ulfHitCount;

	// ---- ①伤害 + ②减速 ----
	for (int i = 0; i < g_ulfHitCount; i++)
	{
		DWORD za = g_ulfHitAddr[i];
		if (MemSafeRead<BYTE>(za + 0xEC)) continue;   // 可能已被前一轮打死
		PVZ::Zombie z(za);
		if (g_ulfDamage > 0)
			z.Hit(g_ulfDamage, PVZ::DAMAGEF_NONE);
		if (g_ulfSlowCs > 0)
			z.Decelerate(g_ulfSlowCs);
	}

	// ---- ③冻结值累计：满值 → 寒冰菇式冻结 → 清零 → 上限 +Step（≤Max）----
	if (g_ulfFreezeGain > 0)
	{
		for (int i = 0; i < g_ulfHitCount; i++)
		{
			DWORD za = g_ulfHitAddr[i];
			if (MemSafeRead<BYTE>(za + 0xEC)) continue;
			int slot = UlfSlot((DWORD)g_ulfHitId[i]);
			if (slot < 0) continue;
			if (g_ulfZombieId[slot] != g_ulfHitId[i])   // 槽位换了新僵尸 → 重置
			{
				g_ulfZombieId[slot] = g_ulfHitId[i];
				g_ulfFreezeVal[slot] = 0;
				g_ulfFreezeCap[slot] = g_ulfFreezeCapBase;
			}
			int val = g_ulfFreezeVal[slot] + g_ulfFreezeGain;
			if (g_ulfFreezeCap[slot] > 0 && val >= g_ulfFreezeCap[slot])
			{
				PVZ::Zombie z(za);
				// 用户澄清："寒冰菇效果"只指僵尸被冻住（寒冰菇的冻结状态），
				// 不带寒冰菇那个白闪 + 霜华满天的爆炸特效 → 这里只调 Froze，不播 0x2A 特效
				z.Froze(g_ulfFreezeCs);
				val = 0;
				int cap = g_ulfFreezeCap[slot] + g_ulfFreezeCapStep;
				if (cap > g_ulfFreezeCapMax) cap = g_ulfFreezeCapMax;
				g_ulfFreezeCap[slot] = cap;
			}
			g_ulfFreezeVal[slot] = val;
		}
	}

	// ---- ④低血魅惑（每只僵尸独立 1% 判定）→ 成功则 3×3 爆炸 ----
	if (g_ulfCharmPercent > 0)
	{
		for (int i = 0; i < g_ulfHitCount; i++)
		{
			DWORD za = g_ulfHitAddr[i];
			if (MemSafeRead<BYTE>(za + 0xEC)) continue;
			PVZ::Zombie z(za);
			if (z.Hypnotized) continue;
			if (!UlfHpBelow(z, g_ulfCharmHpPercent)) continue;
			if ((rand() % 100) >= g_ulfCharmPercent) continue;
			float cx = MemSafeRead<float>(za + 0x2C);
			z.Hypnotize();
			UlfExplode(boardAddr, row, cx, za);
		}
	}

	g_ulfFireRet = 1;   // 已按自研逻辑结算，trampoline 跳过原版 DoRowAreaDamage
}

static void __cdecl UltFumeFire(DWORD plantAddr)
{
	__try
	{
		UltFumeFireImpl(plantAddr);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_ulfFireRet = 0;   // 出异常 → 交还原版，绝不静默 0 伤害
	}
}

// ================= hook 安装 =================
static bool InstallUltFumeHooks()
{
	bool ok = false;

	// ---- Hook A: Plant::FindTargetZombie 0x4675C0 ----
	// 原入口：55 | 8B EC | 83 E4 F8   (push ebp; mov ebp,esp; and esp,0xFFFFFFF8)
	// 入参：[esp+4]=Plant*，[esp+8]=row，ecx=PlantWeapon；返回值 eax=Zombie*；ret 8
	{
		DWORD hookA = 0x4675C0;
		BYTE rawA[6];
		PVZ::Memory::ReadArray<BYTE>(hookA, rawA, 6);
		if (rawA[0] == 0x55 && rawA[1] == 0x8B && rawA[2] == 0xEC &&
			rawA[3] == 0x83 && rawA[4] == 0xE4 && rawA[5] == 0xF8)
		{
			int tramp = (int)TRAMPOLINE_ALLOC();
			if (tramp != 0)
			{
				BYTE tp[256];
				int p = 0;
				auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
				auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
				auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
				auto putNearJcc = [&](BYTE cc) { tp[p++] = 0x0F; tp[p++] = cc; put32(0); };

				// ★ 顺序铁律：先把 Plant* 存进 g_ulfTmpPlant，再拿同一个寄存器去读 SeedType。
				//   （初版写反了：先 mov edx,[edx+0x24] 再 mov [g_ulfTmpPlant],edx，
				//    结果存进去的是 SeedType=10，UltFumeFindTarget 在 <0x10000 守卫处直接 return，
				//    索敌永远返回 0 → FindTargetAndFire 返回 0 → 大喷菇完全不开火。）
				// mov edx,[esp+4]             ; Plant*
				tp[p++] = 0x8B; tp[p++] = 0x54; tp[p++] = 0x24; tp[p++] = 0x04;
				// mov [g_ulfTmpPlant],edx     ; 89 15 imm32 —— 先存地址
				tp[p++] = 0x89; tp[p++] = 0x15; put32((int)&g_ulfTmpPlant);
				// mov edx,[edx+0x24]          ; 再读 SeedType
				tp[p++] = 0x8B; tp[p++] = 0x52; tp[p++] = 0x24;
				// cmp edx,0x0A
				tp[p++] = 0x83; tp[p++] = 0xFA; tp[p++] = 0x0A;
				int jneOrig = p; putNearJcc(0x85);                    // jne ORIG
				tp[p++] = 0x60;                                        // pushad
				putRelCall((DWORD)&UltFumeFindTarget);
				tp[p++] = 0x61;                                        // popad
				// mov eax,[g_ulfTargetRet]    ; A1 imm32
				tp[p++] = 0xA1; put32((int)&g_ulfTargetRet);
				// test eax,eax; jne DONE      ; 找到目标就直接返回
				tp[p++] = 0x85; tp[p++] = 0xC0;
				int jneDone = p; putNearJcc(0x85);
				// --- ORIG：①非大喷菇 ②大喷菇但自研索敌没找到（兜底回退原版 ~3.5 格）---
				// 补回被覆盖的 6 字节后跳 0x4675C6，保证任何自研逻辑出错都只是退化而非"完全不开火"
				// （jne DONE 不跳转时顺序落到 ORIG，正好就是"自研索敌落空 → 回退原版"的兜底）
				int origPos = p;
				*(int*)(tp + jneOrig + 2) = origPos - (jneOrig + 6);
				tp[p++] = 0x55;                                        // push ebp
				tp[p++] = 0x8B; tp[p++] = 0xEC;                        // mov ebp,esp
				tp[p++] = 0x83; tp[p++] = 0xE4; tp[p++] = 0xF8;        // and esp,0xFFFFFFF8
				putRelJmp(0x4675C6);
				// --- DONE：返回自研索敌结果 ---
				int donePos = p;
				*(int*)(tp + jneDone + 2) = donePos - (jneDone + 6);
				tp[p++] = 0xC2; tp[p++] = 0x08; tp[p++] = 0x00;        // ret 8

				PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
				int hookOff = tramp - ((int)hookA + 5);
				BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
				PVZ::Memory::WriteArray<BYTE>(hookA, hook, 5);
				g_ulfHookAState = 1;
				ok = true;
			}
			else
			{
				g_ulfHookAState = -2;      // trampoline 分配失败
			}
		}
		else
		{
			g_ulfHookAState = -1;          // 运行时字节不符（版本不匹配 / 已被别的 hook 占用）
		}
	}

	// ---- Hook B: Plant::Fire 0x466E15 ----
	// 原 5 字节：75 6B | 6A 02 | 55  (jne 0x466E82; push 2; push ebp)，紧接 call DoRowAreaDamage
	// 进入时 eax=SeedType，ebp=Plant*，ebx=variant；非大喷菇必须跳 0x466E82
	{
		DWORD hookB = 0x466E15;
		BYTE rawB[5];
		PVZ::Memory::ReadArray<BYTE>(hookB, rawB, 5);
		if (rawB[0] == 0x75 && rawB[1] == 0x6B && rawB[2] == 0x6A && rawB[3] == 0x02 && rawB[4] == 0x55)
		{
			int tramp = (int)TRAMPOLINE_ALLOC();
			if (tramp != 0)
			{
				BYTE tp[256];
				int p = 0;
				auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
				auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
				auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
				auto putNearJcc = [&](BYTE cc) { tp[p++] = 0x0F; tp[p++] = cc; put32(0); };

				// cmp eax,0x0A
				tp[p++] = 0x83; tp[p++] = 0xF8; tp[p++] = 0x0A;
				int jneOrig = p; putNearJcc(0x85);                     // jne ORIG(=0x466E82)
				// 大喷菇：pushad; push ebp; call UltFumeFire; add esp,4; popad
				// UltFumeFire 把结果写进 g_ulfFireRet（1=已自研结算 / 0=请走原版）。
				// ★ 双出口：返回 0 时必须补执行原版的 push 2 / push ebp / call DoRowAreaDamage，
				//   否则大喷菇会变成 0 伤害且毫无征兆。
				tp[p++] = 0x60;
				tp[p++] = 0x55;                                        // push ebp（植物地址）
				putRelCall((DWORD)&UltFumeFire);
				tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;         // add esp,4（cdecl）
				tp[p++] = 0x61;                                        // popad
				// mov eax,[g_ulfFireRet]
				tp[p++] = 0xA1; put32((int)&g_ulfFireRet);
				// test eax,eax ; jne DONE（已结算 → 跳过原版）
				tp[p++] = 0x85; tp[p++] = 0xC0;
				int jneDone = p; putNearJcc(0x85);
				// --- VANILLA：自研没干成 → 补原版 push 2 / push ebp / call DoRowAreaDamage ---
				tp[p++] = 0x6A; tp[p++] = 0x02;                         // push 2
				tp[p++] = 0x55;                                         // push ebp
				putRelCall(0x45ED00);                                   // call Plant::DoRowAreaDamage
				// DoRowAreaDamage 是 ret 8（callee 清栈），调用方不用 add esp,8
				// --- DONE ---
				int donePos = p;
				*(int*)(tp + jneDone + 2) = donePos - (jneDone + 6);
				tp[p++] = 0x31; tp[p++] = 0xC0;                         // xor eax,eax（无子弹）
				putRelJmp(0x46754C);   // epilogue: pop edi/esi/ebp/ebx; add esp,0x1C; ret 0x10
				// --- ORIG：其它植物，跳原 jne 目标 0x466E82 ---
				int origPos = p;
				*(int*)(tp + jneOrig + 2) = origPos - (jneOrig + 6);
				putRelJmp(0x466E82);

				PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
				int hookOff = tramp - ((int)hookB + 5);
				BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
				PVZ::Memory::WriteArray<BYTE>(hookB, hook, 5);
				g_ulfHookBState = 1;
				ok = true;
			}
			else
			{
				g_ulfHookBState = -2;
			}
		}
		else
		{
			g_ulfHookBState = -1;
		}
	}
	return ok;
}

// 本行是否存在可命中僵尸（仅在冷却结束的那一帧才调用，开销可忽略）
// ★ 与 hook 内一致走限界扫描（UlfScanRow），不分配内存
static bool UlfHasTarget(DWORD boardAddr, DWORD plantAddr)
{
	int row = MemSafeRead<int>(plantAddr + 0x1C);
	int px  = MemSafeRead<int>(plantAddr + 0x8);
	UlfScanRow(boardAddr, row, px);
	return g_ulfHitCount > 0;
}

// 每帧轮询：接管大喷菇的攻击节奏（精确 0.5s 一次，不受 rand 抖动/攻速缩放影响）
static void UpdateUltFumeFrameInner(DWORD boardAddress)
{
	if (!g_ulfEnabled) return;

	g_ulfDbgFrame++;

	// hook 安装（延迟到进关后游戏代码解密就绪，与其它 hook 同模式）
	// ★ 重试 240 帧：一次失败不永久放弃（首帧过早 / trampoline 暂时分配失败都能自愈）。
	//   只有"字节不符(-1)"才停止重试——那是版本不匹配，重试也没用。
	{
		bool needA = (g_ulfHookAState == 0 || g_ulfHookAState == -2);
		bool needB = (g_ulfHookBState == 0 || g_ulfHookBState == -2);
		if ((needA || needB) && g_ulfInstallTries < 240)
		{
			g_ulfInstallTries++;
			InstallUltFumeHooks();
			if (!g_ulfHooksInstalled)
				UlfDebugFlush("after-install");
			g_ulfHooksInstalled = (g_ulfHookAState == 1 || g_ulfHookBState == 1);
		}
	}

	PVZ::Board board(boardAddress);
	auto plants = board.GetAllPlants();
	if (plants.empty()) return;
	int now = MemSafeRead<int>(boardAddress + 0x5568);   // Board.PlayingTime（厘秒）

	int dbgPlants = 0;
	for (auto& plant : plants)
	{
		if (plant.NotExist) continue;
		if ((int)plant.Type != (int)SeedType::Fumeshroom) continue;
		dbgPlants++;
		if (plant.Sleeping) continue;                                 // 睡着不开火（同原版）
		DWORD pa = plant.GetBaseAddress();
		int   pid = plant.Id;
		int   slot = UlfSlot((DWORD)pid);
		if (slot < 0) continue;
		if (g_ulfPlantId[slot] != pid)     // 槽位换了新植株（内存池复用）→ 立即可开火
		{
			g_ulfPlantId[slot] = pid;
			g_ulfPlantLastFire[slot] = -1000000;
		}

		// 上一次的喷射动画还没播完（[plant+0x90] != 0）时必须等待：
		// 中途重新触发会把 ShootingCountdown 重置回 50，导致永远递减不到开火点。
		int shootCd = MemSafeRead<int>(pa + 0x90);
		bool ready = (shootCd == 0) && (now - g_ulfPlantLastFire[slot] >= g_ulfIntervalCs);
		if (ready && UlfHasTarget(boardAddress, pa))
		{
			MemSafeWrite<int>(pa + 0x58, 1);      // 下一 tick 必定开火
			g_ulfPlantLastFire[slot] = now;
			g_ulfDbgTrigger++;
		}
		else
		{
			MemSafeWrite<int>(pa + 0x58, ULF_HOLD_CD);  // 保持等待
		}
	}
	g_ulfDbgPlants = dbgPlants;

	// 每秒落盘一行自检（frame 计数 + hook 状态 + 触发/开火/命中数）
	if ((g_ulfDbgFrame % 100) == 0)
		UlfDebugFlush("tick");
}

// __try 外壳（Inner 含 std::vector，与 __try 同函数会触发 MSVC C2712）
static void UpdateUltFumeFrame(DWORD boardAddress)
{
	__try
	{
		UpdateUltFumeFrameInner(boardAddress);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		// ★ 不能静默：异常被吞掉时整个模块（含 hook 安装）都会失效，
		//   表现为"大喷菇完全是原版"。必须计数并落盘。
		g_ulfDbgErr++;
		if ((g_ulfDbgErr <= 3) || ((g_ulfDbgErr % 100) == 0))
			UlfDebugFlush("exception");
	}
}

// ==================== 大喷菇（Fumeshroom, SeedType=10）等阶机制 ====================
//
// 【规格】
//   · 0阶：同原版
//   · 1/2/4阶：纯攻速（数值在 plant_attack_speed.ini 的 10= 行）
//   · 3阶：攻击范围向前延伸 2 格（FUME_T3_RANGE_EXTEND=160 px），
//          粒子动画同步变长：**只在 3 阶时**额外补喷一段同款雾
//          （FUME_T3_PUFF_DX=160，0-2 阶视觉与原版完全一致）
//   · 5阶：每次攻击命中时把僵尸向后（X 增大）推 FUME_KB_DISTANCE=10 px，
//          位移分摊到 FUME_KB_FRAMES=15 帧内平滑叠加（≈0.25 秒）；
//          处于"抬手要砸"状态（ZombieState::GARGANTUAR_SMASH = 0x46）的巨人免疫
//
// 【逆向依据】（PVZ 1.0.0.1051；反汇编用 pvzdll_s6/pvz_dis.py）
//   1) 攻击矩形 Plant::GetAttackRect 0x467F90，大喷菇专属分支在 0x4680DE：
//        rect.x = ImageX + 0x3C(60)   rect.y = ImageY
//        rect.w = 0x154(340)          rect.h = plant[0x14]
//      索敌 FindTargetZombie 在 0x4675DC、伤害 DoRowAreaDamage 在 0x45ED1E
//      都调这个函数 ⇒ 一处 hook 同时延长"能搜到"和"能打到"的范围。
//   2) 伤害结算 DoRowAreaDamage 0x45ED00 内 0x45EE22 是
//        `call Zombie::TakeDamage(0x5317C0)`（esi=zombie、栈上 damage）。
//      在这一条 call 上记录"真正被本次攻击命中"的僵尸，比在外面重算矩形精确，
//      也不会误推边界外的僵尸。
//   3) ★ 大喷菇不产子弹：Plant::Fire 0x466E00 对 type==0x0A 直接
//        push 2 / push plant / call DoRowAreaDamage + 播 0x1E 音效，然后 ret。
//      通用等阶攻速系统写在 onPlantAddProjectile（子弹创建事件）里 ⇒ 对大喷菇
//      完全无效（plant_attack_speed.ini 的 10= 行原本是死的）。
//      这里每帧钉 [plant+0x5C]（ShootOrProductInterval，UpdateShooter 0x45F8BF
//      读它算 `[plant+0x58] = [plant+0x5C] - rand(0..14)`）实现攻速，
//      按"首次读到的原值 × tierSpeed / 1.5"缩放，不依赖原值绝对值。
//   4) 巨人砸击状态 = ZombieState::GARGANTUAR_SMASH (0x46)；扔小鬼 = 0x45（不免疫）。
//   5) 粒子：UpdateShooting 0x46489C 对 type==0x0A 且 [plant+0x90]==0xF 时
//        push 2 / push row*10000+0x4AF38 / push ImageY+0x1F / push ImageX+0x55
//        call 0x45EEA0（CreateParticleSystem，内部用 edi=Plant 取 LawnApp，
//                       并把新粒子系统 id 写回 plant[0x8C] 用于下次"先销毁上一段"）
//      粒子定义 FumeCloud 是**全局共享**的（emitter 实例只存 def 指针：
//      0x515FE4 `mov [esi],eax`）⇒ 改 .compiled 的扫程会让所有阶一起变长。
//      也不用"额外补喷一段"（两段重叠会把中段叠浓）。
//      最终方案 = **按株隔离**：复制一份 def 数组 + 它后面的 track 数据，
//      重定位内部指针、把 x 轨迹加长，只在该株 3 阶开火时把 def 表项指向副本，
//      创建完立刻指回。实现见 FumePrepareFarDefs / FumeDefSwitch / FumeDefRestore。
//
// 【三个 hook（都先 cmp 植物类型/等阶，非目标原样走原路径）】
//   R) 0x467F90 Plant::GetAttackRect 入口（11 字节）
//      → 3 阶+ 的大喷菇改由 FumeRectFill 自己填矩形（宽 +160），其余原版。
//   K) 0x45EE22 Plant::DoRowAreaDamage 内 call TakeDamage（5 字节 E8 ..）
//      → 5 阶大喷菇命中时登记击退任务；call 本身在 trampoline 内原样补执行。
//   P) 0x4648BB Plant::UpdateShooting 内 call CreateParticleSystem（5 字节 E8 ..）
//      → 3 阶开火时把 FumeCloud 的 def 表项临时指向加长副本，创建后立即指回。
// ============================================================================

#define FUME_KB_SLOTS     64      // 同时排队等待击退的僵尸数上限
#define FUME_BASE_SPEED   1.5f    // 攻速基准（与通用等阶攻速系统一致，= 原版豌豆 1.5s）
#define FUME_STATE_SMASH  0x46    // ZombieState::GARGANTUAR_SMASH

// hook trampoline 与 C++ 之间传参（静态变量，不压栈不分配）
static int   g_fumeRectRet   = 0;
static DWORD g_fumeRectPlant = 0;
static DWORD g_fumeRectOut   = 0;

// 击退任务队列（只存 POD，按僵尸 Id 校验，内存池复用自动失效）
static DWORD g_fumeKbAddr[FUME_KB_SLOTS];
static int   g_fumeKbId[FUME_KB_SLOTS];
static float g_fumeKbRemain[FUME_KB_SLOTS];
static int   g_fumeKbCount = 0;

// 每株的原始射击间隔（ShootOrProductInterval 原值），等阶缩放的分母基准
static std::map<DWORD, int> g_fumeBaseInterval;

// hook 安装状态与自检计数
static int  g_fumeHookRState   = 0;   // 0未装 1已装 -1字节不符 -2tramp分配失败
static int  g_fumeHookKState   = 0;
static int  g_fumeHookPState   = 0;
static int  g_fumeHookTries    = 0;
static int  g_fumeUlfWarned    = 0;
static int  g_fumeDbgFrame     = 0;
static int  g_fumeDbgPlants    = 0;
static int  g_fumeDbgT3        = 0;
static int  g_fumeDbgMaxTier   = 0;   // 最近一帧场上大喷菇的最高等阶
static int  g_fumeDbgPatch     = 0;   // 副本里改到的 x 轨迹节点数（应为 2）
static int  g_fumeDbgSwitch    = 0;   // 3 阶开火时切换到副本的次数
static int  g_fumeDbgMark      = 0;   // 登记击退次数
static int  g_fumeDbgDone      = 0;   // 走完一次完整击退的僵尸数
static int  g_fumeDbgDrop      = 0;   // 僵尸提前消失/复用而丢弃
static int  g_fumeDbgErr       = 0;

// 3 阶粒子用的 FumeCloud 加长副本（按株隔离的核心状态，实现见文件后段）
static DWORD g_fumeDefsOrig    = 0;   // 原版 emitterDefs 指针
static DWORD g_fumeDefsFar     = 0;   // 加长副本（VirtualAlloc，进程内常驻）
static DWORD g_fumeDefSlot     = 0;   // &defArray[effectId]（[+0] 即 emitterDefs）
static int   g_fumeDefState    = 0;   // 0未准备 1就绪 -1失败
static int   g_fumeDefSwitched = 0;
static int   g_fumeDbgReloc    = 0;   // 副本里重定位的指针个数

// 极简 itoa（不碰 CRT，与 UltFume 段同款：hook/帧内禁用 CRT）
static void FumeItoa(int v, char* out)
{
	char tmp[16];
	int n = 0;
	int neg = 0;
	if (v < 0) { neg = 1; v = (v == -2147483647 - 1) ? 2147483647 : -v; }
	if (v == 0) tmp[n++] = '0';
	while (v > 0 && n < 15) { tmp[n++] = (char)('0' + (v % 10)); v /= 10; }
	int p = 0;
	if (neg) out[p++] = '-';
	while (n > 0) out[p++] = tmp[--n];
	out[p] = 0;
}

static void FumeDebugFlush(const char* tag)
{
	if (!g_fumeDebug) return;
	char buf[512];
	int p = 0;
#define FUME_PUTS(s) do { const char* _s = (s); while (*_s && p < 470) buf[p++] = *_s++; } while (0)
#define FUME_PUTN(v) do { char _t[16]; FumeItoa((int)(v), _t); const char* _s2 = _t; while (*_s2 && p < 470) buf[p++] = *_s2++; } while (0)
	FUME_PUTS("[FUME build 20261020-v1] ");
	FUME_PUTS(tag);
	FUME_PUTS(" enabled="); FUME_PUTN(g_fumeEnabled);
	FUME_PUTS(" ulf=");     FUME_PUTN(g_ulfEnabled);
	FUME_PUTS(" hookR=");   FUME_PUTN(g_fumeHookRState);
	FUME_PUTS(" hookK=");   FUME_PUTN(g_fumeHookKState);
	FUME_PUTS(" hookP=");   FUME_PUTN(g_fumeHookPState);
	FUME_PUTS(" defst=");   FUME_PUTN(g_fumeDefState);
	FUME_PUTS(" patch=");   FUME_PUTN(g_fumeDbgPatch);
	FUME_PUTS(" reloc=");   FUME_PUTN(g_fumeDbgReloc);
	FUME_PUTS(" frame=");   FUME_PUTN(g_fumeDbgFrame);
	FUME_PUTS(" plants=");  FUME_PUTN(g_fumeDbgPlants);
	FUME_PUTS(" maxtier="); FUME_PUTN(g_fumeDbgMaxTier);
	FUME_PUTS(" switch=");  FUME_PUTN(g_fumeDbgSwitch);
	FUME_PUTS(" t3=");      FUME_PUTN(g_fumeDbgT3);
	FUME_PUTS(" mark=");    FUME_PUTN(g_fumeDbgMark);
	FUME_PUTS(" done=");    FUME_PUTN(g_fumeDbgDone);
	FUME_PUTS(" drop=");    FUME_PUTN(g_fumeDbgDrop);
	FUME_PUTS(" err=");     FUME_PUTN(g_fumeDbgErr);
	FUME_PUTS(" ext=");     FUME_PUTN(g_fumeRangeExtend);
	FUME_PUTS(" kb=");      FUME_PUTN(g_fumeKbDistance);
	FUME_PUTS("/");         FUME_PUTN(g_fumeKbFrames);
	FUME_PUTS("\r\n");
#undef FUME_PUTS
#undef FUME_PUTN
	buf[p] = 0;

	HANDLE h = CreateFileA("D:\\pvz_fume_debug.txt", GENERIC_WRITE, FILE_SHARE_READ,
		NULL, OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
	if (h != INVALID_HANDLE_VALUE)
	{
		SetFilePointer(h, 0, NULL, FILE_BEGIN);
		DWORD written = 0;
		WriteFile(h, buf, (DWORD)p, &written, NULL);
		CloseHandle(h);
	}
}

// 当前等阶（0-5）；查不到经验记录按 0 阶
static int FumeTierOf(DWORD plantAddr)
{
	auto it = g_plantExperience.find((int)plantAddr);
	int exp = (it != g_plantExperience.end()) ? it->second : 0;
	return GetPlantTier((int)SeedType::Fumeshroom, exp);
}

static void FumeResetAll()
{
	g_fumeKbCount = 0;
	for (int i = 0; i < FUME_KB_SLOTS; i++)
	{
		g_fumeKbAddr[i] = 0;
		g_fumeKbId[i] = 0;
		g_fumeKbRemain[i] = 0.0f;
	}
	g_fumeBaseInterval.clear();
	g_fumeRectRet = 0;
	// 万一正好停在"已切到加长副本"的瞬间（指针未恢复），这里强制指回原版
	if (g_fumeDefSwitched && g_fumeDefSlot != 0)
	{
		MemSafeWrite<DWORD>(g_fumeDefSlot, g_fumeDefsOrig);
		g_fumeDefSwitched = 0;
	}
}

// ================= Hook R：3 阶攻击矩形延伸 =================
// 由 trampoline 调用（入参在 g_fumeRectPlant / g_fumeRectOut）
// ★ 填成功置 g_fumeRectRet=1；任何不确定都置 0 交还原版（绝不静默改错范围）
static void FumeRectFill()
{
	g_fumeRectRet = 0;
	if (!g_fumeEnabled) return;
	DWORD pa = g_fumeRectPlant;
	DWORD out = g_fumeRectOut;
	if (pa < 0x10000 || out < 0x10000) return;
	if (MemSafeRead<int>(pa + 0x24) != (int)SeedType::Fumeshroom) return;
	if (g_fumeRangeExtend <= 0) return;
	if (FumeTierOf(pa) < 3) return;

	int ix = MemSafeRead<int>(pa + 0x08);   // ImageX
	int iy = MemSafeRead<int>(pa + 0x0C);   // ImageY
	int hh = MemSafeRead<int>(pa + 0x14);   // 高度（原版直接用 plant[0x14]）
	MemSafeWrite<int>(out + 0,  ix + 0x3C);                    // 与原版一致：右移 60
	MemSafeWrite<int>(out + 4,  iy);
	MemSafeWrite<int>(out + 8,  0x154 + g_fumeRangeExtend);    // 340 + 160 = 500
	MemSafeWrite<int>(out + 12, hh);
	g_fumeRectRet = 1;
	g_fumeDbgT3++;
}

// ================= Hook K：5 阶命中即登记击退 =================
// 由 trampoline 调用（cdecl，plant=ebp、zombie=ebx）
static void __cdecl FumeKnockMark(DWORD plantAddr, DWORD zombieAddr)
{
	if (!g_fumeEnabled) return;
	if (g_fumeKbDistance <= 0) return;
	if (plantAddr < 0x10000 || zombieAddr < 0x10000) return;
	if (MemSafeRead<int>(plantAddr + 0x24) != (int)SeedType::Fumeshroom) return;
	if (FumeTierOf(plantAddr) < 5) return;
	if (MemSafeRead<BYTE>(zombieAddr + 0xEC)) return;              // NotExist
	if (MemSafeRead<int>(zombieAddr + 0x28) == FUME_STATE_SMASH) return;  // 巨人抬手砸：免疫

	int id = MemSafeRead<int>(zombieAddr + 0x158);                 // Zombie.Id
	for (int i = 0; i < g_fumeKbCount; i++)                        // 已在队列 → 累加剩余距离
	{
		if (g_fumeKbId[i] == id && g_fumeKbAddr[i] == zombieAddr)
		{
			g_fumeKbRemain[i] += (float)g_fumeKbDistance;
			g_fumeDbgMark++;
			return;
		}
	}
	if (g_fumeKbCount >= FUME_KB_SLOTS) return;
	g_fumeKbAddr[g_fumeKbCount]   = zombieAddr;
	g_fumeKbId[g_fumeKbCount]     = id;
	g_fumeKbRemain[g_fumeKbCount] = (float)g_fumeKbDistance;
	g_fumeKbCount++;
	g_fumeDbgMark++;
}

// ================= 3 阶粒子扫程（按株隔离：整块复制 def + track 并重定位指针）=================
// 【为什么要复制】
//   粒子定义 FumeCloud 全局共享；emitter 实例创建时只记 def 项指针
//   （0x515FE4 `mov [esi],eax`），参数不复制。def 项 0x164(356) 字节装不下
//   21 个 track 节点（420 字节）⇒ track 数据在 def 数组之外的独立区域，
//   只复制 def 项等于没改。所以整块复制（def 数组 + 尾部 FUME_DEF_BLOCK_EXTRA），
//   再把 def 项里指向原块的指针重定位到副本。
// 【怎么做到只对 3 阶生效】
//   hook 0x4648BB（原版创建粒子那条 call）：3 阶植物开火时先把
//   defArray[FumeCloud].emitterDefs 指向副本 → 调用原版创建 → 立刻指回原版。
//   已创建的实例各自保存 def 项指针，所以 0-2 阶永远用原版块，互不影响。
// 【安全设计】
//   · 重定位只处理 def 项区域内、4 字节对齐、且值落在原块范围内的 DWORD；
//     track 节点是纯 float、不含指针，不会被误改。
//   · 副本里找不到那 2 个 x 轨迹节点（说明 track 不在这段连续内存里）⇒
//     放弃整个方案，3 阶粒子保持原版长度，日志里 patch=0，绝不硬改数据。
//   · trampoline 无条件调用 FumeDefRestore，指针绝不残留。
#define FUME_DEF_ITEM_SIZE    0x164
#define FUME_DEF_BLOCK_EXTRA  0x2000

// 按名字查粒子类型的 effectId（粒子参数表 {int effect; const char* name}）
static int FumeFindEffectId(const char* defName)
{
	int paramCount = MemSafeRead<int>(0x6A9F10);
	DWORD paramArr = MemSafeRead<DWORD>(0x6A9F14);
	if (!paramArr || paramCount <= 0 || paramCount > 4096) return -1;
	for (int i = 0; i < paramCount; i++)
	{
		DWORD namePtr = MemSafeRead<DWORD>(paramArr + i * 8 + 4);
		if (!SeaBurstStrContains(namePtr, defName)) continue;
		int effectId = MemSafeRead<int>(paramArr + i * 8);
		if (effectId >= 0 && effectId <= 512) return effectId;
	}
	return -1;
}

// 准备"加长版 FumeCloud 定义"（一次性；失败则 3 阶粒子保持原版长度）
static void FumePrepareFarDefs()
{
	if (g_fumeDefState != 0) return;
	g_fumeDefState = -1;
	if (g_fumeT3PuffDx <= 0) return;

	DWORD defArr = MemSafeRead<DWORD>(0x6A9F0C);
	if (defArr < 0x10000) return;
	int effectId = FumeFindEffectId("FumeCloud");
	if (effectId < 0) return;
	DWORD defs = MemSafeRead<DWORD>(defArr + effectId * 8);
	int   cnt  = MemSafeRead<int>(defArr + effectId * 8 + 4);
	if (defs < 0x10000 || cnt <= 0 || cnt > 8) return;

	const int blockLen = FUME_DEF_ITEM_SIZE * cnt + FUME_DEF_BLOCK_EXTRA;
	if (!CrashIsReadable(defs, blockLen)) return;

	BYTE* buf = (BYTE*)VirtualAlloc(NULL, blockLen, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
	if (!buf) return;
	memcpy(buf, (const void*)defs, blockLen);

	// ① 重定位 def 项内部指向"原块"的指针（track 节点不含指针，不会被误改）
	int reloc = 0;
	for (int off = 0; off + 4 <= FUME_DEF_ITEM_SIZE * cnt; off += 4)
	{
		DWORD v = 0;
		memcpy(&v, buf + off, 4);
		if (v < defs || v >= defs + (DWORD)blockLen) continue;
		if ((v & 3) != 0) continue;
		DWORD nv = (DWORD)buf + (v - defs);
		memcpy(buf + off, &nv, 4);
		reloc++;
	}

	// ② 在副本里把 x 轨迹两个节点加长（节点起点不一定 4 字节对齐 ⇒ 逐字节扫描 + memcpy 读）
	int patched = 0;
	for (int off = 0; off + 12 <= blockLen; off++)
	{
		float t = 0.0f, lo = 0.0f, hi = 0.0f;
		memcpy(&t,  buf + off,     4);
		memcpy(&lo, buf + off + 4, 4);
		memcpy(&hi, buf + off + 8, 4);
		if (t > 0.55f && t < 0.65f && lo > 10.0f && lo < 40.0f && hi > 200.0f && hi < 400.0f)
		{
			float nv = hi + (float)g_fumeT3PuffDx;
			memcpy(buf + off + 8, &nv, 4);
			patched++;
		}
		else if (t > 0.95f && t < 1.05f && lo > 15.0f && lo < 40.0f && hi > 200.0f && hi < 400.0f)
		{
			float nv = hi + (float)g_fumeT3PuffDx;
			memcpy(buf + off + 8, &nv, 4);
			patched++;
		}
	}
	g_fumeDbgPatch = patched;
	g_fumeDbgReloc = reloc;

	if (patched < 2)
	{
		// track 不在这一段连续内存里 ⇒ 复制带不走 track，方案放弃（宁可不加长，也不乱改）
		VirtualFree(buf, 0, MEM_RELEASE);
		return;
	}

	g_fumeDefsOrig = defs;
	g_fumeDefsFar  = (DWORD)buf;
	g_fumeDefSlot  = defArr + effectId * 8;
	g_fumeDefState = 1;
}

// hook 调用：3 阶 → 把 def 表项指向加长副本（返回后必须调 FumeDefRestore）
static void __cdecl FumeDefSwitch(DWORD plantAddr)
{
	g_fumeDefSwitched = 0;
	if (!g_fumeEnabled) return;
	if (plantAddr < 0x10000) return;
	if (MemSafeRead<int>(plantAddr + 0x24) != (int)SeedType::Fumeshroom) return;
	if (FumeTierOf(plantAddr) < 3) return;
	if (g_fumeDefState == 0) FumePrepareFarDefs();
	if (g_fumeDefState != 1) return;
	MemSafeWrite<DWORD>(g_fumeDefSlot, g_fumeDefsFar);
	g_fumeDefSwitched = 1;
	g_fumeDbgSwitch++;
}

// hook 调用：指回原版（无条件调用，未切换时什么都不做）
static void __cdecl FumeDefRestore()
{
	if (!g_fumeDefSwitched) return;
	MemSafeWrite<DWORD>(g_fumeDefSlot, g_fumeDefsOrig);
	g_fumeDefSwitched = 0;
}

// ================= hook 安装 =================
static bool InstallFumeHooks()
{
	bool ok = false;

	// ---- Hook R: Plant::GetAttackRect 0x467F90（11 字节）----
	// 原字节：8B 11 (mov edx,[ecx]) | 56 (push esi) | 33 F6 (xor esi,esi)
	//         39 B2 68 07 00 00 (cmp [edx+0x768],esi)
	// 入参：ecx=Plant*，eax=Rect*，[esp+4]=flag；返回 ret 4
	{
		DWORD hookR = 0x467F90;
		static const BYTE kExpR[11] = { 0x8B,0x11, 0x56, 0x33,0xF6,
		                                0x39,0xB2,0x68,0x07,0x00,0x00 };
		BYTE raw[11];
		PVZ::Memory::ReadArray<BYTE>(hookR, raw, 11);
		if (memcmp(raw, kExpR, 11) == 0)
		{
			int tramp = (int)TRAMPOLINE_ALLOC();
			if (tramp != 0)
			{
				BYTE tp[512];
				int p = 0;
				auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
				auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
				auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
				auto putNearJcc = [&](BYTE cc) { tp[p++] = 0x0F; tp[p++] = cc; put32(0); };

				// cmp dword [ecx+0x24],0x0A   ; 非大喷菇直接走原版
				tp[p++] = 0x83; tp[p++] = 0x79; tp[p++] = 0x24; tp[p++] = 0x0A;
				int jneOrig = p; putNearJcc(0x85);
				// mov [g_fumeRectPlant],ecx / mov [g_fumeRectOut],eax
				tp[p++] = 0x89; tp[p++] = 0x0D; put32((int)&g_fumeRectPlant);
				tp[p++] = 0xA3; put32((int)&g_fumeRectOut);
				// pushad; call FumeRectFill; popad
				tp[p++] = 0x60;
				putRelCall((DWORD)&FumeRectFill);
				tp[p++] = 0x61;
				// mov eax,[g_fumeRectOut]     ; 恢复 eax = Rect*
				tp[p++] = 0xA1; put32((int)&g_fumeRectOut);
				// cmp dword [g_fumeRectRet],0 ; 0 → 交还原版
				tp[p++] = 0x83; tp[p++] = 0x3D; put32((int)&g_fumeRectRet); tp[p++] = 0x00;
				int jneDone = p; putNearJcc(0x85);
				// --- ORIG：重放 11 字节后跳 0x467F9B ---
				int origPos = p;
				*(int*)(tp + jneOrig + 2) = origPos - (jneOrig + 6);
				for (int i = 0; i < 11; i++) tp[p++] = kExpR[i];
				putRelJmp(0x467F9B);
				// --- DONE：已按自研矩形返回 ---
				int donePos = p;
				*(int*)(tp + jneDone + 2) = donePos - (jneDone + 6);
				tp[p++] = 0xC2; tp[p++] = 0x04; tp[p++] = 0x00;   // ret 4

				PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
				int hookOff = tramp - ((int)hookR + 5);
				BYTE hook[11];
				hook[0] = 0xE9; memcpy(hook + 1, &hookOff, 4);
				memset(hook + 5, 0x90, 6);
				PVZ::Memory::WriteArray<BYTE>(hookR, hook, 11);
				g_fumeHookRState = 1;
				ok = true;
			}
			else g_fumeHookRState = -2;
		}
		else g_fumeHookRState = -1;
	}

	// ---- Hook K: Plant::DoRowAreaDamage 内 0x45EE22 `call Zombie::TakeDamage`（5 字节）----
	// 原字节：E8 99 29 0D 00（call 0x5317C0）；进入时 ebp=Plant*、ebx=Zombie*、esi=Zombie*
	{
		DWORD hookK = 0x45EE22;
		static const BYTE kExpK[5] = { 0xE8,0x99,0x29,0x0D,0x00 };
		BYTE raw[5];
		PVZ::Memory::ReadArray<BYTE>(hookK, raw, 5);
		if (memcmp(raw, kExpK, 5) == 0)
		{
			int tramp = (int)TRAMPOLINE_ALLOC();
			if (tramp != 0)
			{
				BYTE tp[256];
				int p = 0;
				auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
				auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
				auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
				auto putNearJcc = [&](BYTE cc) { tp[p++] = 0x0F; tp[p++] = cc; put32(0); };

				// cmp dword [ebp+0x24],0x0A  ; 只有大喷菇才登记（ebp 在 DoRowAreaDamage 内恒为 Plant*）
				tp[p++] = 0x83; tp[p++] = 0x7D; tp[p++] = 0x24; tp[p++] = 0x0A;
				int jneSkip = p; putNearJcc(0x85);
				// pushad; push ebp(plant); push ebx(zombie); call FumeKnockMark; add esp,8; popad
				tp[p++] = 0x60;
				tp[p++] = 0x55;
				tp[p++] = 0x53;
				putRelCall((DWORD)&FumeKnockMark);
				tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x08;
				tp[p++] = 0x61;
				// --- SKIP ---
				int skipPos = p;
				*(int*)(tp + jneSkip + 2) = skipPos - (jneSkip + 6);
				// 原样补执行 call Zombie::TakeDamage（esi=Zombie*，[esp]=damage 已由原代码压好）
				tp[p++] = 0xB8; put32(0x5317C0);      // mov eax,0x5317C0
				tp[p++] = 0xFF; tp[p++] = 0xD0;        // call eax
				putRelJmp(0x45EE27);

				PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
				int hookOff = tramp - ((int)hookK + 5);
				BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
				PVZ::Memory::WriteArray<BYTE>(hookK, hook, 5);
				g_fumeHookKState = 1;
				ok = true;
			}
			else g_fumeHookKState = -2;
		}
		else g_fumeHookKState = -1;
	}

	// ---- Hook P: Plant::UpdateShooting 内 0x4648BB `call CreateParticleSystem`（5 字节）----
	// 原字节：E8 E0 A5 FF FF（call 0x45EEA0）；进入时 edi=Plant*，栈上 4 个参数已就绪
	// （X=ImageX+0x55、Y=ImageY+0x1F、renderOrder=row*10000+0x4AF38、type=2）
	// 流程：先把 3 阶植物的 def 表项切到加长副本 → 原样调用创建 → 立刻切回原版。
	{
		DWORD hookP = 0x4648BB;
		static const BYTE kExpP[5] = { 0xE8,0xE0,0xA5,0xFF,0xFF };
		BYTE raw[5];
		PVZ::Memory::ReadArray<BYTE>(hookP, raw, 5);
		if (memcmp(raw, kExpP, 5) == 0)
		{
			int tramp = (int)TRAMPOLINE_ALLOC();
			if (tramp != 0)
			{
				BYTE tp[256];
				int p = 0;
				auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
				auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
				auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

				// pushad; push edi(Plant*); call FumeDefSwitch; add esp,4; popad
				tp[p++] = 0x60;
				tp[p++] = 0x57;
				putRelCall((DWORD)&FumeDefSwitch);
				tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;
				tp[p++] = 0x61;
				// 原样调用 CreateParticleSystem（参数已在栈上，ret 0x10 由被调方清栈）
				tp[p++] = 0xB8; put32(0x45EEA0);       // mov eax,0x45EEA0
				tp[p++] = 0xFF; tp[p++] = 0xD0;         // call eax
				// 立刻切回原版（无条件，未切换时内部直接返回）
				tp[p++] = 0x60;                         // pushad
				putRelCall((DWORD)&FumeDefRestore);
				tp[p++] = 0x61;                         // popad
				putRelJmp(0x4648C0);

				PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
				int hookOff = tramp - ((int)hookP + 5);
				BYTE hook[5] = { 0xE9 }; memcpy(hook + 1, &hookOff, 4);
				PVZ::Memory::WriteArray<BYTE>(hookP, hook, 5);
				g_fumeHookPState = 1;
				ok = true;
			}
			else g_fumeHookPState = -2;
		}
		else g_fumeHookPState = -1;
	}
	return ok;
}

// ================= 每帧轮询 =================
static void FumeTierFrameInner(DWORD boardAddress)
{
	if (!g_fumeEnabled) return;

	// ★ 与究极大喷菇（UltFume）互斥：ULF 开着时大喷菇已被改造成"全行/100伤/冻结/魅惑"，
	//   两套系统会各自结算一遍伤害并抢 [plant+0x58] 节奏 ⇒ 本模块整体停用。
	if (g_ulfEnabled)
	{
		if (!g_fumeUlfWarned)
		{
			g_fumeUlfWarned = 1;
			FumeDebugFlush("skip:ULF_ENABLED=1");
		}
		return;
	}

	g_fumeDbgFrame++;

	// hook 延迟安装（游戏代码运行时才解密）；字节不符(-1)不重试
	{
		bool needR = (g_fumeHookRState == 0 || g_fumeHookRState == -2);
		bool needK = (g_fumeHookKState == 0 || g_fumeHookKState == -2);
		bool needP = (g_fumeHookPState == 0 || g_fumeHookPState == -2);
		if ((needR || needK || needP) && g_fumeHookTries < 240)
		{
			g_fumeHookTries++;
			InstallFumeHooks();
			FumeDebugFlush("after-install");
		}
	}

	const DWORD PLANT_SIZE = 0x14C;
	int plantArray = MemSafeRead<int>(boardAddress + 0xAC);
	int plantCount = MemSafeRead<int>(boardAddress + 0xB0);
	int dbgPlants = 0;
	int maxTier   = 0;

	if (plantArray > 0x10000 && plantCount > 0 && plantCount < 1024)
	{
		for (int i = 0; i < plantCount; i++)
		{
			DWORD p = (DWORD)(plantArray + i * PLANT_SIZE);
			if (MemSafeRead<BYTE>(p + 0x141)) continue;                     // NotExist
			if (MemSafeRead<int>(p + 0x24) != (int)SeedType::Fumeshroom) continue;
			dbgPlants++;

			int tier = FumeTierOf(p);
			if (tier > maxTier) maxTier = tier;

			// ---- 攻速：按等阶缩放射击间隔重装基数 [plant+0x5C] ----
			// UpdateShooter 0x45F8BF：mov ecx,[esi+0x5C] / sub ecx,rand(15) / mov [esi+0x58],ecx
			// ⇒ 间隔 = 0x5C - rand(0..14)。钉住 0x5C 即可精确控制攻速，且保留原版随机抖动。
			float sp = GetPlantAttackSpeed((int)SeedType::Fumeshroom, tier);
			if (sp > 0.0f)
			{
				auto bit = g_fumeBaseInterval.find(p);
				if (bit == g_fumeBaseInterval.end())
				{
					// 首次见到该植株：此刻的 0x5C 还是原版值（本模块还没写过）
					int base = MemSafeRead<int>(p + 0x5C);
					if (base < 1 || base > 3000) base = 150;   // 兜底：按原版 1.5s=150 tick
					g_fumeBaseInterval[p] = base;
					bit = g_fumeBaseInterval.find(p);
				}
				int base = bit->second;
				int want = (int)((float)base * sp / FUME_BASE_SPEED + 0.5f);
				if (want < 1) want = 1;
				if (MemSafeRead<int>(p + 0x5C) != want)
					MemSafeWrite<int>(p + 0x5C, want);
			}
		}
	}
	g_fumeDbgPlants = dbgPlants;
	g_fumeDbgMaxTier = maxTier;
	// 注：3 阶粒子加长不走每帧轮询 —— 由 Hook P 在创建粒子时按株切 def 副本，
	//     所以这里不需要任何"按最高等阶统一调整"的动作。

	// ---- 5 阶击退：把剩余位移分摊到 FUME_KB_FRAMES 帧，每帧叠加 step 像素 ----
	if (g_fumeKbCount > 0)
	{
		int   frames = (g_fumeKbFrames > 0) ? g_fumeKbFrames : 1;
		float step   = (float)g_fumeKbDistance / (float)frames;
		if (step < 0.01f) step = 0.01f;
		int w = 0;
		for (int i = 0; i < g_fumeKbCount; i++)
		{
			DWORD za = g_fumeKbAddr[i];
			bool valid = (za >= 0x10000)
				&& !MemSafeRead<BYTE>(za + 0xEC)                        // NotExist
				&& (MemSafeRead<int>(za + 0x158) == g_fumeKbId[i]);      // Id 校验（防内存池复用）
			if (!valid)
			{
				g_fumeDbgDrop++;
				continue;
			}
			float remain = g_fumeKbRemain[i];
			float take   = (step < remain) ? step : remain;
			float x      = MemSafeRead<float>(za + 0x2C);                // Zombie.X
			MemSafeWrite<float>(za + 0x2C, x + take);                    // 向右（后退）推
			remain -= take;
			if (remain > 0.004f)
			{
				g_fumeKbAddr[w]   = za;
				g_fumeKbId[w]     = g_fumeKbId[i];
				g_fumeKbRemain[w] = remain;
				w++;
			}
			else g_fumeDbgDone++;
		}
		g_fumeKbCount = w;
	}

	if ((g_fumeDbgFrame % 100) == 0)
		FumeDebugFlush("tick");
}

// __try 外壳（Inner 含 std::map，与 __try 同函数会触发 MSVC C2712）
static void UpdateFumeTierFrame(DWORD boardAddress)
{
	__try
	{
		FumeTierFrameInner(boardAddress);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_fumeDbgErr++;
		if ((g_fumeDbgErr <= 3) || ((g_fumeDbgErr % 100) == 0))
			FumeDebugFlush("exception");
	}
}

// ==================== 坚果墙（Wallnut）等阶机制：每帧轮询 ====================
// 仅一项工作：升级瞬间回满血（Hp=MaxHp；坚果墙破损贴图按 HP 比例自动恢复完整）。
// 已移除死亡留保龄球/亡语机制。全部可读写任意游戏对象（轮询帧铁律），
// 异常由 WallnutTierFrame 的 __try 兜底。

static void WallnutTierFrameInner(DWORD boardAddr)
{
	if (!CrashIsReadable(boardAddr, 0x100)) return;
	const DWORD PLANT_SIZE = 0x14C;
	int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
	int plantCount = MemSafeRead<int>(boardAddr + 0xB0);
	if (!plantArray || plantCount <= 0) return;

	for (int i = 0; i < plantCount; i++)
	{
		DWORD p = (DWORD)(plantArray + i * PLANT_SIZE);
		if (MemSafeRead<BYTE>(p + 0x141)) continue;                        // NotExist
		if (MemSafeRead<int>(p + 0x24) != (int)SeedType::Wallnut) continue;

		int exp = 0;
		auto eit = g_plantExperience.find(p);
		if (eit != g_plantExperience.end()) exp = eit->second;
		int tier = GetPlantTier((int)SeedType::Wallnut, exp);

		int last = g_wallnutCurTier[p];    // operator[] 不存在时默认 0
		if (tier > last)
		{
			int maxHp = MemSafeRead<int>(p + 0x44);
			MemSafeWrite<int>(p + 0x40, maxHp);
		}
		g_wallnutCurTier[p] = tier;
	}
}

// __try 外壳（无局部对象；实体在 Inner，避开 C2712）
static void WallnutTierFrame(DWORD boardAddr)
{
	__try
	{
		WallnutTierFrameInner(boardAddr);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ==================== 高坚果（Tallnut）等阶机制：hook 处理函数 ====================
// ★hook 帧内：只做指针读写 + map 查找（同 ChomperBiteDamage 先例），禁 CRT 重活。
// 公共判定：高坚果且 2阶+（3阶满阶所以 >=2 即"有抗秒杀"）且扣血后仍能存活 →
// 扣 TALLNUT_ANTIKILL_Dmg 血并返回 1（调用方拦截原版秒杀）；否则返回 0 放行原版。
// ★ 大蒜共用入口：3阶大蒜 → 不扣血直接返回 1（完全免疫碾压/砸击）。
static int __cdecl TallnutAbsorbKill(DWORD plantAddr)
{
	if (plantAddr < 0x10000) return 0;
	// ---- 磁力菇 1 阶护盾：任何植物身上有护盾 → 消耗整个护盾抵挡一次秒杀（植物不死）----
	// ★ 车辆碾压（0x52E920）判定为 1 时，调用方 TallnutVehicleCrushBlock 会顺带把车击退一段，
	//   与本需求「车类碾压抵挡时同时击退车」完全一致，无需额外处理。
	if (MagShieldAbsorbKill(plantAddr)) return 1;
	// ---- 大蒜 3 阶：完全免疫（不扣血、不消失）----
	// ★ GARLIC_ENABLED=0 时一并放行原版碾压（整段大蒜机制停用的排障口径）
	if (g_garlicEnabled && MemSafeRead<int>(plantAddr + 0x24) == (int)SeedType::Garlic)
	{
		int gexp = 0;
		auto git = g_plantExperience.find(plantAddr);
		if (git != g_plantExperience.end()) gexp = git->second;
		return (GetPlantTier((int)SeedType::Garlic, gexp) >= 3) ? 1 : 0;
	}
	if (MemSafeRead<int>(plantAddr + 0x24) != (int)SeedType::Tallnut) return 0;
	int exp = 0;
	auto it = g_plantExperience.find(plantAddr);
	if (it != g_plantExperience.end()) exp = it->second;
	if (GetPlantTier((int)SeedType::Tallnut, exp) < 2) return 0;
	int hp = MemSafeRead<int>(plantAddr + 0x40);
	if (hp <= g_tallnutAntiKillDmg) return 0;   // 撑不住这一次 → 原版压扁/烧毁
	MemSafeWrite<int>(plantAddr + 0x40, hp - g_tallnutAntiKillDmg);
	return 1;
}

// HookB 处理：Plant::Squish(0x462B80) 入口，ecx=植物。
// 覆盖巨人锤击/压扁头（SquishAllInSquare type=0 逐株调用）与僵王踩踏（直接调用）。
static int __cdecl TallnutSquishProtect(DWORD plantAddr)
{
	return TallnutAbsorbKill(plantAddr);
}

// HookA 处理：Zombie::SquishAllInSquare(0x52E920) 入口（__thiscall 调用方清栈 ret 0xC）。
// zombie=车类僵尸（edi），attackType=1 仅车类碾压（CheckSquish 路径）；
// row/col=碾压格。格内有能扛住的 2阶+ 高坚果 → 逐株扣血 + 车类击退 1 格 + 整格拦截
// （同格南瓜头/花盆一并被保护——车被顶回去本次碾压不发生）。
static int __cdecl TallnutVehicleCrushBlock(DWORD zombieAddr, int attackType, int gridRow, int gridCol)
{
	if (zombieAddr < 0x10000 || attackType != 1) return 0;
	if (gridRow < 0 || gridRow > 5 || gridCol < 0 || gridCol > 8) return 0;
	DWORD boardAddr = MemSafeRead<DWORD>(zombieAddr + 4);
	if (!boardAddr) return 0;
	int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
	int plantCount = MemSafeRead<int>(boardAddr + 0xB0);
	if (!plantArray || plantCount <= 0) return 0;

	int protectedAny = 0;
	const DWORD PLANT_SIZE = 0x14C;
	for (int i = 0; i < plantCount; i++)
	{
		DWORD p = (DWORD)(plantArray + i * PLANT_SIZE);
		if (MemSafeRead<BYTE>(p + 0x141)) continue;      // NotExist
		if (MemSafeRead<int>(p + 0x1C) != gridRow) continue;
		if (MemSafeRead<int>(p + 0x28) != gridCol) continue;
		if (TallnutAbsorbKill(p)) protectedAny = 1;
	}
	if (!protectedAny) return 0;
	// 车类击退 1 格（X += 80，向后退 = X 增大；同子弹击退写法）
	float zx = MemSafeRead<float>(zombieAddr + 0x2C);
	zx += (float)TALLNUT_VEHICLE_KB_PX;
	if (zx < 0.0f) zx = 0.0f;
	MemSafeWrite<float>(zombieAddr + 0x2C, zx);
	return 1;
}

// HookC 处理：辣椒僵尸爆炸烧毁调用点（0x527729 call Plant::Die）。
// eax=将被烧毁的植物。返回 1=拦截烧毁（已在 TallnutAbsorbKill 里扣血）。
static int __cdecl TallnutJalaProtect(DWORD plantAddr)
{
	return TallnutAbsorbKill(plantAddr);
}

// 安装 HookA @0x52E920（83 EC 08 8B 57 04，rawLen=6，跳回 hookAddr+6）
// 布局：pushad; 依次 push gridCol/gridRow/attackType/zombie(edi);
//       call TallnutVehicleCrushBlock; add esp,0x10; test eax,eax; popad;
//       jne BLOCKED(ret 0xC) / ORIG(原6字节 + jmp hookAddr+6)
// ★test 在 popad 之前（popad 不动 flags，jne 用 test 的 ZF）；ORIG 首指令引用 edi（popad 已恢复）。
static bool InstallTallnutSquishHookA()
{
	DWORD hookAddr = 0x52E920;
	static const BYTE kExpected[6] = { 0x83, 0xEC, 0x08, 0x8B, 0x57, 0x04 };

	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 6);
	if (memcmp(raw, kExpected, 6) != 0)
		return false;                       // 运行时字节不符（未解密/版本不符）→ 下帧重试

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return false;

	BYTE tp[64];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                  // pushad
	// ★实证（调用方 0x52ee71: push 1/row/col；函数内 [esp+0x14]=col、[esp+0x18]=row、[esp+0x1C]=attackType）：
	// 入口栈 [esp+4]=col、[esp+8]=row、[esp+0xC]=attackType
	// → pushad 后 [esp+0x24]=col、[esp+0x28]=row、[esp+0x2C]=attackType。
	// pushad 帧寄存器：[esp]=edi、+4=esi、+8=ebp、+0xC=原esp、+0x10=ebx、+0x14=edx、+0x18=ecx、+0x1C=eax。
	// edi 自 hook 入口起未被改动 = 原 zombie，直接 push edi 传参。
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x24; // push [esp+0x24] gridCol=col
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x2C; // push [esp+0x2C] gridRow=row（esp 已-4：0x24+4+4）
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x34; // push [esp+0x34] attackType（esp 已-8）
	tp[p++] = 0x57;                                  // push edi（=原 zombie）
	putRelCall((DWORD)&TallnutVehicleCrushBlock);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x10;  // add esp,0x10
	tp[p++] = 0x85; tp[p++] = 0xC0;                  // test eax,eax
	tp[p++] = 0x61;                                  // popad（不破坏 flags）
	tp[p++] = 0x75; tp[p++] = 0x0B;                  // jne BLOCKED（+11：ORIG 3+3 + jmp 5）

	// ---- ORIG：原 6 字节 + 跳回 ----
	tp[p++] = 0x83; tp[p++] = 0xEC; tp[p++] = 0x08;  // sub esp,8
	tp[p++] = 0x8B; tp[p++] = 0x57; tp[p++] = 0x04;  // mov edx,[edi+4]
	putRelJmp(hookAddr + 6);

	// ---- BLOCKED：调用方清栈（thiscall ret 0xC）----
	tp[p++] = 0xC2; tp[p++] = 0x0C; tp[p++] = 0x00;  // ret 0xC

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	return true;
}

// 安装 HookB @0x462B80（53 55 8B 6C 24 0C，rawLen=6，跳回 hookAddr+6）
// 布局：pushad; push [esp+0x24](植物栈参, Squish=thatcall ret 4); call TallnutSquishProtect;
//       add esp,4; test eax,eax; popad; jne BLOCKED(ret) / ORIG(原6字节 + jmp 回)
static bool InstallTallnutSquishHookB()
{
	DWORD hookAddr = 0x462B80;
	static const BYTE kExpected[6] = { 0x53, 0x55, 0x8B, 0x6C, 0x24, 0x0C };

	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 6);
	if (memcmp(raw, kExpected, 6) != 0)
		return false;

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return false;

	BYTE tp[64];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                  // pushad
	// ★实证：Plant::Squish 是 thatcall ret 4（函数尾两处 C2 04 00；调用方 0x52e97a push ecx 当栈参）。
	// 入口 [esp]=ret、[esp+4]=植物栈参 → pushad 后 [esp+0x24]=植物。
	// （[esp+4] 是 pushad 保存的 esi，不是植物——上一版就是错在这里。）
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x24; // push [esp+0x24] 植物(栈参)
	putRelCall((DWORD)&TallnutSquishProtect);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;  // add esp,4
	tp[p++] = 0x85; tp[p++] = 0xC0;                  // test eax,eax
	tp[p++] = 0x61;                                  // popad
	tp[p++] = 0x75; tp[p++] = 0x0B;                  // jne BLOCKED（+11：ORIG 1+1+4 + jmp 5）

	// ---- ORIG ----
	tp[p++] = 0x53;                                  // push ebx
	tp[p++] = 0x55;                                  // push ebp
	tp[p++] = 0x8B; tp[p++] = 0x6C; tp[p++] = 0x24; tp[p++] = 0x0C; // mov ebp,[esp+0xC]
	putRelJmp(hookAddr + 6);

	// ---- BLOCKED ----
	tp[p++] = 0xC2; tp[p++] = 0x04; tp[p++] = 0x00;  // ret 4（Squish 自清 4 字节栈参，必须同款）

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	return true;
}

// 安装 HookC @0x527729（E8 rel32 = call 0x4679B0，整条 call 替换为 jmp，无需跳回）
// 布局：pushad; push [esp+0x20](0x527728 push eax 留下的植物参); call TallnutJalaProtect; add esp,4;
//       test eax,eax; popad; jne SKIP; call 0x4679B0(原烧毁); SKIP: jmp 0x52772E
static bool InstallTallnutJalaHook()
{
	DWORD hookAddr = 0x527729;

	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 5);
	if (raw[0] != 0xE8)
		return false;
	int rel = *(int*)(raw + 1);
	if ((DWORD)(hookAddr + 5 + rel) != 0x4679B0)
		return false;                       // 不是预期的 Plant::Die 调用 → 不动

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return false;

	BYTE tp[48];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                  // pushad
	// ★实证：0x527728 push eax(植物) 在 call 之前 → 入口 [esp]=植物参、[esp+4]=ret
	// → pushad 后 [esp+0x20]=植物参。（[esp+0] 是 pushad 保存的 edi，不是植物——上一版错在这里。）
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x20; // push [esp+0x20] 植物(栈参)
	putRelCall((DWORD)&TallnutJalaProtect);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;  // add esp,4
	tp[p++] = 0x85; tp[p++] = 0xC0;                  // test eax,eax
	tp[p++] = 0x61;                                  // popad
	tp[p++] = 0x75; tp[p++] = 0x0A;                  // jne SKIP（+10：call 5 + jmp 5）
	putRelCall(0x4679B0);                            // ORIG：烧毁（Die ret 4 自清栈参数）
	putRelJmp(0x52772E);                             // ORIG 完毕直接回原流程（不进 SKIP 的 add）
	// ---- SKIP ----
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;  // add esp,4（清掉 0x527728 push eax 留下的参数）
	putRelJmp(0x52772E);                             // 拦截路径回原流程

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	return true;
}

// ==================== 高坚果（Tallnut）等阶机制：每帧轮询 ====================
// ① 血量阶梯：T0=4000 / T1+=配置上限；上限提升瞬间回满血（即 0→1 升级回满，规格定死）
// ② 3阶累计受伤（HP 帧间差值，含秒杀转化的扣血）→ 每满 2000 击退前方1格内最近僵尸
//    击退在轮询帧结算（hook 只拦截秒杀），全对象可读写（轮询帧铁律）
static void TallnutKnockFrontZombie(DWORD plantAddr)
{
	DWORD boardAddr = MemSafeRead<DWORD>(plantAddr + 4);
	if (!boardAddr) return;
	int row = MemSafeRead<int>(plantAddr + 0x1C);
	int col = MemSafeRead<int>(plantAddr + 0x28);
	if (row < 0 || row > 5) return;
	int maxnum = MemSafeRead<int>(boardAddr + 0x94);
	DWORD zbase = MemSafeRead<DWORD>(boardAddr + 0x90);
	if (maxnum <= 0 || maxnum > 1024) return;
	if (zbase < 0x10000 || !CrashIsReadable(zbase, 0x15C * 8)) return;

	float plantX = (float)(col * 80 + 40);           // 格中心像素 X（同玉米投手 dist 算法）
	const float FRONT_WIN = 80.0f;                   // 前方1格（+10px 容差覆盖正贴脸啃食者）
	DWORD best = 0;
	float bestDist = 1e9f;
	for (int i = 0; i < maxnum; i++)
	{
		DWORD za = zbase + 0x15C * (DWORD)i;
		if (MemSafeRead<BYTE>(za + 0xEC)) continue;   // NotExist
		if (MemSafeRead<BYTE>(za + 0xB8)) continue;   // 被魅惑的不打
		if (MemSafeRead<int>(za + 0x1C) != row) continue;
		if (MemSafeRead<int>(za + 0xC8) <= 0) continue; // 已死亡/濒死
		float zx = MemSafeRead<float>(za + 0x2C);
		float d = zx - plantX;
		if (d < -10.0f || d > FRONT_WIN) continue;
		if (d < bestDist) { bestDist = d; best = za; }
	}
	if (!best) return;
	float nx = MemSafeRead<float>(best + 0x2C) + (float)TALLNUT_T3_KB_PX;
	if (nx < 0.0f) nx = 0.0f;
	MemSafeWrite<float>(best + 0x2C, nx);
}

static void TallnutFrameInner(DWORD boardAddr)
{
	if (!CrashIsReadable(boardAddr, 0x100)) return;
	const DWORD PLANT_SIZE = 0x14C;
	int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
	int plantCount = MemSafeRead<int>(boardAddr + 0xB0);
	if (!plantArray || plantCount <= 0) return;

	for (int i = 0; i < plantCount; i++)
	{
		DWORD p = (DWORD)(plantArray + i * PLANT_SIZE);
		if (MemSafeRead<BYTE>(p + 0x141)) continue;      // NotExist
		if (MemSafeRead<int>(p + 0x24) != (int)SeedType::Tallnut) continue;

		int exp = 0;
		auto eit = g_plantExperience.find(p);
		if (eit != g_plantExperience.end()) exp = eit->second;
		int tier = GetPlantTier((int)SeedType::Tallnut, exp);

		// ---- 1) 血量阶梯（T1 上限提升瞬间回满血）----
		int wantMax = (tier >= 1) ? g_tallnutT1MaxHp : TALLNUT_T0_MAXHP;
		int curMax = MemSafeRead<int>(p + 0x44);
		if (curMax != wantMax)
		{
			int hp = MemSafeRead<int>(p + 0x40);
			if (wantMax > curMax) hp = wantMax;      // 上调上限 → 回满血（规格：1阶回满）
			else if (hp > wantMax) hp = wantMax;     // 下调 → 封顶
			MemSafeWrite<int>(p + 0x44, wantMax);
			MemSafeWrite<int>(p + 0x40, hp);
		}

		// ---- 2) 3阶：累计受伤 → 击退 ----
		int curHp = MemSafeRead<int>(p + 0x40);
		auto lit = g_tallnutLastHp.find(p);
		int lastHp = (lit != g_tallnutLastHp.end()) ? lit->second : curHp; // 首帧不回溯旧伤
		if (tier >= 3 && curHp < lastHp)
		{
			int& acc = g_tallnutDmgAcc[p];
			acc += lastHp - curHp;
			while (acc >= TALLNUT_T3_DMG_STEP)
			{
				acc -= TALLNUT_T3_DMG_STEP;
				TallnutKnockFrontZombie(p);
			}
		}
		g_tallnutLastHp[p] = curHp;
		g_tallnutCurTier[p] = tier;
	}
}

// __try 外壳（无局部对象；实体在 Inner，避开 C2712）
static void TallnutFrame(DWORD boardAddr)
{
	__try
	{
		TallnutFrameInner(boardAddr);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ==================== 大蒜（Garlic, SeedType=36）等阶机制 ====================
// 详见文件头"大蒜等阶机制"注释块。本段职责：
//   ① 1阶血量阶梯（每帧轮询，上调上限瞬间回满血）
//   ② 2阶换行方向：读鼠标右击切换 + 关卡行约束 + 换行 patch（GarlicPickRow）
//   ③ 2阶箭头绘制（DrawUITop 层，随植物位置每帧重算）
//   ④ 3阶免疫碾压：巨人"不砸"（改两条 call 目标）+ 车类碾压统一入口免疫
//      （0x52E920 已在 TallnutVehicleCrushBlock 首段并分支，见该函数）
//
// ★★ 本段 2026-10-16 重写：旧实现有三处硬伤，导致 2/3 阶静默失效 ——
//   1) 两处把 `zombie+0x1C` 当行号（僵尸 +0x1C 是动画计时器，行号在 +0x130）⇒
//      GarlicPickRow 拿到的行号是垃圾 ⇒ 找不到大蒜 ⇒ 恒返回 -1 回退原版随机；
//   2) 用 `zombie+0x80`（蹦极目标列）当列号定位"正在啃的大蒜" ⇒ 恒不匹配；
//   3) 方向只有"被约束改写"一条路径 ⇒ 约束行的方向与箭头显示可能错位。
//
// ---- 大蒜诊断日志（GARLIC_DEBUG=1；只用 CreateFileA/WriteFile，无 CRT）----
static void GarlicLog(const char* s)
{
	if (!g_garlicDebug) return;
	HANDLE h = CreateFileA("D:\\pvz_garlic.log", FILE_APPEND_DATA,
		FILE_SHARE_READ | FILE_SHARE_WRITE, NULL,
		OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
	if (h == INVALID_HANDLE_VALUE) return;
	DWORD written = 0;
	WriteFile(h, s, (DWORD)lstrlenA(s), &written, NULL);
	CloseHandle(h);
}
#define GARLIC_LOGP(s)     do { GarlicLog(s); } while (0)
#define GARLIC_LOGN(v)     do { GarlicLogInt((int)(v)); } while (0)
#define GARLIC_LOGL(s)     do { GarlicLog(s); GarlicLog("\r\n"); } while (0)
static void GarlicItoa(int v, char* out)
{
	char tmp[16]; int n = 0, neg = 0;
	if (v < 0) { neg = 1; v = (v == -2147483647 - 1) ? 2147483647 : -v; }
	if (v == 0) tmp[n++] = '0';
	while (v > 0 && n < 15) { tmp[n++] = (char)('0' + (v % 10)); v /= 10; }
	int p = 0;
	if (neg) out[p++] = '-';
	while (n > 0) out[p++] = tmp[--n];
	out[p] = 0;
}
static void GarlicLogInt(int v)
{
	char t[16];
	GarlicItoa(v, t);
	GarlicLog(t);
}

// ---- 大蒜方向与关卡行约束 ----
// 本关实际行数：五行（白天/黑夜/屋顶/月夜）= 5，六行（泳池/迷雾）= 6
static int GarlicMapRows(DWORD boardAddr)
{
	int scene = MemSafeRead<int>(boardAddr + 0x554C);   // LevelScene
	return (scene == (int)SceneType::Pool || scene == (int)SceneType::Fog) ? 6 : 5;
}

// 关卡行约束：返回该行是否强制方向；强制时写入 *outDir（GARLIC_UP / GARLIC_DOWN）。
// 五行（rows=5）: 第1行(row 0)→向下，第5行(row 4)→向上，其余可自由切换；
// 六行（rows=6）: 第1/3/5行(row 0/2/4)→向下，第2/4/6行(row 1/3/5)→向上（奇数行→向上）。
static int GarlicRowConstraint(int boardAddr, int row, int* outDir)
{
	int rows = GarlicMapRows(boardAddr);
	if (row < 0 || row >= rows) return 0;
	if (rows == 6)
	{
		*outDir = (row % 2 == 0) ? GARLIC_DOWN : GARLIC_UP;
		return 1;
	}
	if (row == 0) { *outDir = GARLIC_DOWN; return 1; }   // 五行第1行 → 只能向下
	if (row == 4) { *outDir = GARLIC_UP;   return 1; }   // 五行第5行 → 只能向上
	return 0;
}

// 方向合法性：把"行约束"统一表达成一行判别式（六行图：上=奇数行，下=偶数行；
// 五行图：第0行只能下、第4行只能上，其余都合法）
static bool GarlicDirIsValid(int rows, int row, int dir)
{
	if (row < 0 || row >= rows) return false;
	if (rows == 6) return (dir == GARLIC_UP) ? (row % 2 == 1) : (row % 2 == 0);
	if (row == 0) return dir == GARLIC_DOWN;
	if (row == 4) return dir == GARLIC_UP;
	return true;
}

// 玩家偏好方向 → 被关卡约束后的实际方向（箭头与换行都用它）
static int GarlicClampDir(DWORD boardAddr, int row, int dir)
{
	int rows = GarlicMapRows(boardAddr);
	dir = (dir == GARLIC_UP) ? GARLIC_UP : GARLIC_DOWN;
	if (GarlicDirIsValid(rows, row, dir)) return dir;
	return dir ? GARLIC_DOWN : GARLIC_UP;   // 被约束 → 只剩另一个方向
}

// 植物当前 Id（+0x148，不可读 = 0）——地址 + Id 双重匹配，防内存池复用串档
static int GarlicPlantId(DWORD plantAddr)
{
	if (plantAddr < 0x10000 || !CrashIsReadable(plantAddr + 0x148, 4))
		return 0;
	return MemSafeRead<int>(plantAddr + 0x148);
}

// 查槽位（未登记返回 GARLIC_SLOT_NONE）
static int GarlicSlotFind(DWORD plantAddr)
{
	int id = GarlicPlantId(plantAddr);
	for (int i = 0; i < g_garlicCount; i++)
		if (g_garlic[i].addr == plantAddr && g_garlic[i].id == id)
			return i;
	return GARLIC_SLOT_NONE;
}

// 查/建槽位；满则 -1。新株初始方向 = 向上（需求：初始为向上）
static int GarlicSlotEnsure(DWORD plantAddr)
{
	int i = GarlicSlotFind(plantAddr);
	if (i != GARLIC_SLOT_NONE) return i;
	if (plantAddr < 0x10000 || g_garlicCount >= GARLIC_SLOT_MAX) return GARLIC_SLOT_NONE;
	i = g_garlicCount++;
	g_garlic[i].addr = plantAddr;
	g_garlic[i].id   = GarlicPlantId(plantAddr);
	g_garlic[i].dir  = GARLIC_UP;
	return i;
}

// 取"玩家偏好方向"（未登记 = 向上）
static int GarlicPrefDir(DWORD plantAddr)
{
	int i = GarlicSlotFind(plantAddr);
	return (i == GARLIC_SLOT_NONE) ? GARLIC_UP : g_garlic[i].dir;
}

// 取大蒜当前"实际生效方向"（唯一出口；箭头与换行都走它）
static int GarlicEffectiveDir(DWORD boardAddr, DWORD plant)
{
	int row = MemSafeRead<int>(plant + 0x1C);
	return GarlicClampDir(boardAddr, row, GarlicPrefDir(plant));
}

// 大蒜帧计数器（诊断心跳 / 槽位清理节流）
static int g_garlicFrameTick = 0;

// 每帧清理未登记/已被顶替的槽位（紧凑化，避免槽位耗尽）
static void GarlicPruneSlots(DWORD boardAddr)
{
	for (int i = g_garlicCount - 1; i >= 0; i--)
	{
		DWORD p = g_garlic[i].addr;
		bool alive = (MemSafeRead<int>(p + 0x24) == (int)SeedType::Garlic)
			&& (MemSafeRead<BYTE>(p + 0x141) == 0)
			&& (MemSafeRead<int>(p + 0x148) == g_garlic[i].id);
		if (alive) continue;
		g_garlic[i] = g_garlic[g_garlicCount - 1];
		g_garlicCount--;
	}
}

// ---- 格子像素几何（Board::PixelToGridY 0x41C550 反汇编实证，全项目统一常量）----
//   列像素区间: [25 + col*80, 25 + col*80 + 80)，列 = (X - 25) / 80
// ★★ 为什么不用游戏原生 Board::PixelToGridX(0x41C4C0)（2026-10-16 崩溃实证后改）：
//   该函数内部连解 4 层指针（[board+0x8C] → [+0x7F8] → [+0x81C]…），任何一层陈旧/半销毁
//   就直接 AV；而且它**不保存 EBX**（push ebx 后把 ebx 当工作寄存器，出口 pop ebx 只恢复
//   自己压的那个值 ⇒ 实际吃掉调用方的 EBX）。在"僵尸换行"这种 hook 帧里调用它，实测造成
//   "僵尸啃咬大蒜瞬间崩溃"（崩溃栈里有 `call GarlicPickRow` 的返回址 + 0x52BD09 帧）。
//   ⇒ 大蒜段一律用整数换算，**不在 hook 帧里调用任何游戏函数**。
static int GarlicColFromPixelX(int x)
{
	int col = (x - 25) / 80;         // C 整除向零取整，负数结果 ≥ 0，天然安全
	if (col < 0) col = 0;
	if (col > 8) col = 8;
	return col;
}

// ---- 找出"某僵尸正在啃的那株大蒜"（2阶+）----
// 定位依据（全部反汇编实证）：
//   ① 同格优先：由僵尸像素 X 换算出所在列（GarlicColFromPixelX，无函数调用），
//      再要求该格大蒜的格中心 X 与僵尸 X 相差 ≤ 0.65 格（52px）——"正在啃"必然贴脸。
//      绝不能用 zombie+0x80：那是蹦极目标列（PVZ.h 注释 BungeeColumn）。
//   ② 兜底相邻格：换行瞬间僵尸可能已跨到前一格，再放宽到 ±1 格，取 X 最近的一株。
//   ③ 只在"僵尸行"与"上下相邻行"里找（大蒜换行只会被本行/相邻行的僵尸触发）。
// 返回植物地址；找不到返回 0。
static DWORD GarlicFindEating(DWORD boardAddr, DWORD zombieAddr)
{
	int zrow = GarlicZombieRow(zombieAddr);
	if (zrow < 0 || zrow > 5) return 0;

	int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
	int plantCount = MemSafeRead<int>(boardAddr + 0xB0);
	if (!plantArray || plantCount <= 0) return 0;

	float zx = MemSafeRead<float>(zombieAddr + 0x2C);   // 僵尸实际 X（像素）
	int zcol = GarlicColFromPixelX((int)zx);

	const DWORD PLANT_SIZE = 0x14C;
	// ★ 不要用 near/far/exact 当变量名：MSVC 把 near/far 当旧式关键字，exact 亦冲突（已踩 C2059）
	DWORD bestExact = 0, bestNear = 0;
	float bestExactD = 1e9f, bestNearD = 1e9f;
	for (int i = 0; i < plantCount; i++)
	{
		DWORD p = (DWORD)(plantArray + i * PLANT_SIZE);
		if (MemSafeRead<BYTE>(p + 0x141)) continue;                       // NotExist
		if (MemSafeRead<int>(p + 0x24) != (int)SeedType::Garlic) continue;
		int prow = MemSafeRead<int>(p + 0x1C);
		if (prow != zrow && prow != zrow - 1 && prow != zrow + 1) continue;
		int pcol = MemSafeRead<int>(p + 0x28);
		float pcx = (float)(pcol * 80 + 40);                              // 格中心 X
		float d = pcx - zx; if (d < 0.0f) d = -d;
		bool sameCell = (pcol == zcol && prow == zrow);
		if (!sameCell && d > 52.0f) continue;                             // 不在贴脸范围内
		if (sameCell && d < bestExactD) { bestExactD = d; bestExact = p; }
		if (d < bestNearD)              { bestNearD  = d; bestNear  = p; }
	}
	DWORD best = bestExact ? bestExact : bestNear;
	if (!best) return 0;

	// 2阶+ 才接管方向（0/1 阶完全走原版随机换行）
	int exp = 0;
	auto eit = g_plantExperience.find(best);
	if (eit != g_plantExperience.end()) exp = eit->second;
	return (GetPlantTier((int)SeedType::Garlic, exp) >= 2) ? best : 0;
}

// ---- 换行决策（由 patch 调用；edi=僵尸，栈上两字节：向上可用/向下可用）----
// 调用约定：__cdecl(DWORD zombieAddr, int upAvail, int downAvail) → 返回目标行号；-1 = 不接管
//   ① 找出该僵尸正在啃的大蒜（2阶+）
//   ② 指定方向可用 → 走指定方向；否则走另一边
//   ③ 两边都不可用 → 返回原行（移动 0，等价原版"不变"）
// ★★ hook 帧内的二次保险：本函数被 hook 直接 call，任何未捕获异常都会把游戏带走
//    （2026-10-16 实测过一次"僵尸啃咬大蒜瞬间崩溃"）。因此实体全部包在 __try 里，
//    异常一律按"不接管"处理（返回 -1 走原版随机），绝不让异常穿出 hook。
// ★ 必须 noinline：__try 作用域内不能出现需要对象展开的局部对象（C2712 铁律，
//   同本文件"实体拆 Inner"的既有做法）。Inner 里有 std::map 迭代器，绝不能被内联进来。
static __declspec(noinline) int GarlicPickRowInner(DWORD zombieAddr, int upAvail, int downAvail)
{
	g_garlicPickCalls++;
	// ---- 诊断：前若干次无条件记录输入与"为什么没接管"，用于定位 picks>0 但 writes==0 ----
	//   （只读字段，不调用任何游戏函数；上限 40 行防刷屏）
	int rowRaw = -1;
	int earlyOut = 1;                  // 1=僵尸地址非法 2=行号越界 3=Board 为空 0=未提前返回
	DWORD boardAddr = 0;
	do {
		if (zombieAddr < 0x10000) break;
		rowRaw = MemSafeRead<int>(zombieAddr + ZOMBIE_ROW_OFFSET);
		if (rowRaw < 0 || rowRaw > 5) { earlyOut = 2; break; }
		boardAddr = MemSafeRead<DWORD>(zombieAddr + 4);
		if (!boardAddr) { earlyOut = 3; break; }
		earlyOut = 0;
	} while (0);

	if (g_garlicDebug && g_garlicPickCalls <= 40)
	{
		GARLIC_LOGP("[garlic] pick#"); GARLIC_LOGN(g_garlicPickCalls);
		GARLIC_LOGP(" z=0x");  GARLIC_LOGN(zombieAddr);
		GARLIC_LOGP(" row130="); GARLIC_LOGN(rowRaw);
		GARLIC_LOGP(" board=0x"); GARLIC_LOGN(boardAddr);
		GARLIC_LOGP(" up=");   GARLIC_LOGN(upAvail);
		GARLIC_LOGP(" down="); GARLIC_LOGN(downAvail);
		GARLIC_LOGP(" early="); GARLIC_LOGN(earlyOut);
		GARLIC_LOGL("");
	}
	if (earlyOut == 1) { g_garlicEarlyAddr++; return -1; }
	if (earlyOut == 2) { g_garlicEarlyRow++;  return -1; }
	if (earlyOut == 3) { g_garlicEarlyBoard++; return -1; }
	int row = rowRaw;

	DWORD plant = GarlicFindEating(boardAddr, zombieAddr);
	if (!plant)
	{
		g_garlicNoTarget++;
		if (g_garlicDebug && g_garlicNoTarget <= 8)
		{
			int zxInt = (int)MemSafeRead<float>(zombieAddr + 0x2C);
			GARLIC_LOGP("[garlic] pick: no target zrow="); GARLIC_LOGN(row);
			GARLIC_LOGP(" zx="); GARLIC_LOGN(zxInt);
			GARLIC_LOGP(" zcol="); GARLIC_LOGN(GarlicColFromPixelX(zxInt));
			GARLIC_LOGP(" up="); GARLIC_LOGN(upAvail);
			GARLIC_LOGP(" down="); GARLIC_LOGN(downAvail);
			GARLIC_LOGL("");
		}
		return -1;               // 非2阶大蒜 → 交回原版随机分支
	}

	int dir = GarlicEffectiveDir(boardAddr, plant);
	// 按指定方向挑行
	int target;
	if (dir == GARLIC_UP)
	{
		if (upAvail)        target = row - 1;
		else if (downAvail) target = row + 1;
		else                target = row;
	}
	else
	{
		if (downAvail)      target = row + 1;
		else if (upAvail)   target = row - 1;
		else                target = row;
	}
	// ★ 行号合法性再确认一次：原版只会 ±1 或不动；超出 [0,5] 一律不接管
	//   （写坏僵尸行号会连带写坏 [z+0x20] 图层，是"越写越乱"型崩溃的源头）
	if (target < 0 || target > 5) return -1;

	g_garlicRowWrites++;
	if (g_garlicDebug && g_garlicRowWrites <= 12)
	{
		GARLIC_LOGP("[garlic] pick: row="); GARLIC_LOGN(row);
		GARLIC_LOGP(" dir=");  GARLIC_LOGN(dir);
		GARLIC_LOGP(" -> ");   GARLIC_LOGN(target);
		GARLIC_LOGP(" plant="); GARLIC_LOGN(plant);
		GARLIC_LOGL("");
	}
	return target;
}

static int __cdecl GarlicPickRow(DWORD zombieAddr, int upAvail, int downAvail)
{
	__try
	{
		return GarlicPickRowInner(zombieAddr, upAvail, downAvail);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_garlicNoTarget++;
		return -1;               // 异常 → 交回原版随机，绝不让异常穿出 hook
	}
}

// ---- 大蒜换行 patch 安装 ----
// 原代码 0x52B902 起 24 字节（"两边都可用"时的随机 ±1 分支）：
//   B8 02 00 00 00          mov eax,2
//   E8 F4 3A 08 00          call 0x5AF400 (Rand)
//   85 C0                   test eax,eax
//   75 06                   jne 0x52B916
//   83 47 1C 01             add dword [edi+0x1C],1      (向下)
//   EB 04                   jmp 0x52B91C
//   83 47 1C FF             add dword [edi+0x1C],-1     (向上)
// 跳回 0x52B91A（重算图层）。该点无内部跳转目标（前一字节 0x52B901 是 ret）。
// 替换为：push 上可用/下可用/edi → call GarlicPickRow → -1 走原版分支，否则直接写行号。
static bool InstallGarlicRowHook()
{
	DWORD hookAddr = 0x52B902;
	static const BYTE kExpected[24] = {
		0xB8, 0x02, 0x00, 0x00, 0x00,
		0xE8, 0xF4, 0x3A, 0x08, 0x00,
		0x85, 0xC0,
		0x75, 0x06,
		0x83, 0x47, 0x1C, 0x01,
		0xEB, 0x04,
		0x83, 0x47, 0x1C, 0xFF
	};
	BYTE raw[24];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 24);
	if (memcmp(raw, kExpected, 24) != 0)
		return false;                    // 运行时字节不符（未解密/版本不符）→ 下帧重试

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return false;

	BYTE tp[128];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                  // pushad（保护全部寄存器；edi 保持=僵尸）
	// ★ 偏移换算：入口 esp = E。pushad 压 0x20 字节 → 新 esp = E-0x20。
	//   原 [E+0x17]（上可用）→ pushad 后 [esp+0x37]；原 [E+0x16]（下可用）→ [esp+0x36]。
	//   pushad 帧内：[esp]=edi、+4=esi、+8=ebp、+0xC=原esp、+0x10=ebx、+0x14=edx、+0x18=ecx、+0x1C=eax
	tp[p++] = 0x0F; tp[p++] = 0xB6; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x37; // movzx eax, byte [esp+0x37] 上可用
	tp[p++] = 0x50;                                  // push eax
	tp[p++] = 0x0F; tp[p++] = 0xB6; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x3A; // movzx eax, byte [esp+0x3A] 下可用（栈已 -4）
	tp[p++] = 0x50;                                  // push eax
	tp[p++] = 0x57;                                  // push edi（僵尸）
	putRelCall((DWORD)&GarlicPickRow);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x0C;  // add esp,0xC
	tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x1C; // mov [esp+0x1C],eax（pushad 的 eax 槽）
	tp[p++] = 0x61;                                  // popad（eax 被恢复为返回值）

	// 返回值判定：-1 = 非大蒜/不由本函数接管 → 走原版随机分支
	tp[p++] = 0x83; tp[p++] = 0xF8; tp[p++] = 0xFF;  // cmp eax, -1
	tp[p++] = 0x74;                                  // je ORIG（rel8 占位，写入后回填）
	int jeRelPos = p; p += 1;

	// ---- 接管：直接写行号 ----
	tp[p++] = 0x89; tp[p++] = 0x47; tp[p++] = 0x1C;  // mov [edi+0x1C], eax
	putRelJmp(0x52B91A);                             // jmp 重算图层

	// ---- ORIG：原 24 字节分支 + 跳回 ----
	int origStart = p;
	memcpy(tp + p, kExpected, 24); p += 24;
	putRelJmp(0x52B91A);

	// 回填 je 的 rel8：目标 = origStart，基准 = jeRelPos+1
	tp[jeRelPos] = (BYTE)(origStart - (jeRelPos + 1));

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);

	// 装后回读校验（.text 若为只读，写入静默失败 → 必须当场发现）
	BYTE verify[5];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, verify, 5);
	return (verify[0] == 0xE9 && memcmp(verify + 1, hook + 1, 4) == 0);
}

// ---- HookD：3阶大蒜免疫"碾压/砸击"（巨人锤击 + 车类碾压的统一出口）----
// 反汇编实证（2026-10-16 复核，本 exe 版本 1.0.0.1051）：
//   ① Plant::Squish = 0x462B80（`53 55 8B 6C 24 0C` = push ebx/push ebp/mov ebp,[esp+0xC]，
//      thiscall，函数尾 `C2 04 00` = ret 4）。**全 exe 的碾压/砸扁唯一出口**：
//      - 巨人扫格遍历器 A 0x534B90 在 0x534BDC `push edx; call 0x462B80`
//      - 巨人扫格遍历器 B 0x534FF0 在 0x53502E `push edx; call 0x462B80`
//      - 车类碾压 Zombie::SquishAllInSquare 0x52E920 内 `0x52E97A push ecx; call 0x462B80`
//   ② 因此只要把 0x462B80 的**入口**接管（本文件高坚果 HookB 已装），
//      三条路径全部被覆盖 —— 大蒜 3 阶的"不压扁"在这一个点上就能拿到。
//   ③ 「巨人无视大蒜、不抬手砸」还要额外把两条遍历器 call 直接跳过，
//      否则巨人仍会播"抬手砸"动作（虽然大蒜不会消失）。两条 call 各自独立可失败。
// 本函数即 HookB 的判定回调（与高坚果共用 0x462B80 入口，不重复安装 hook）。
// 返回 1 = 跳过本次 Squish（大蒜毫发无损）；0 = 放行原版。
#define PLANT_SQUISH_ADDR 0x462B80      // 原版 Plant::Squish（1.0.0.1051）
static int __cdecl GarlicSmashSkipCheck(DWORD plantAddr)
{
	if (plantAddr < 0x10000) return 0;
	if (MemSafeRead<int>(plantAddr + 0x24) != (int)SeedType::Garlic) return 0;
	int exp = 0;
	auto it = g_plantExperience.find(plantAddr);
	if (it != g_plantExperience.end()) exp = it->second;
	return (GetPlantTier((int)SeedType::Garlic, exp) >= 3) ? 1 : 0;
}

// 转调原版 Plant::Squish；3阶大蒜直接跳过（thiscall ret 4 语义必须保持）
static void __declspec(naked) GarlicAwareSquish()
{
	__asm
	{
		// 入口：[esp]=ret、[esp+4]=植物栈参；ecx=植物
		pushad
		push dword ptr [esp + 0x24]   // 植物栈参（pushad 后 +0x24）
		mov  ebx, GarlicSmashSkipCheck
		call ebx                      // __cdecl(DWORD plant) → eax: 1=跳过
		add  esp, 4
		test eax, eax
		popad
		jne  SKIP_SQUISH2

		// 非3阶大蒜 → 转调原版 Plan::Squish（保持原栈帧语义：ret 4）
		mov  ebx, PLANT_SQUISH_ADDR
		call ebx
		ret  4

	SKIP_SQUISH2:
		// 跳过：不砸。仍需按 thiscall ret 4 清栈
		ret  4
	}
}

// 改写 call 目标：把 `push edx; call 0x462B80` 中的 rel32 重定向到 GarlicAwareSquish
// ★ 幂等：若那条 call 已经指向 GarlicAwareSquish（本函数重复调用 / 上局已改过），
//   原样返回 true，不再重复改（旧版在这里返回 false，导致 smashHook 被误标 -1 放弃）。
static bool PatchGarlicSmashCall(DWORD callAddr)
{
	BYTE raw[7];
	PVZ::Memory::ReadArray<BYTE>(callAddr, raw, 7);
	static const BYTE kPushEdx = 0x52;
	static const BYTE kCall = 0xE8;
	if (raw[0] != kPushEdx || raw[1] != kCall)
		return false;
	int rel = 0;
	memcpy(&rel, raw + 2, 4);
	DWORD curTarget = (DWORD)(callAddr + 7 + rel);
	if (curTarget == (DWORD)&GarlicAwareSquish)
		return true;                        // 已经是我们的目标 → 幂等成功
	if (curTarget != PLANT_SQUISH_ADDR)
		return false;                       // 目标既不是原版 Squish 也不是我们 → 版本不符，跳过

	BYTE patch[7];
	patch[0] = kPushEdx;
	patch[1] = kCall;
	int newRel = (int)((DWORD)&GarlicAwareSquish - (callAddr + 7));
	memcpy(patch + 2, &newRel, 4);
	PVZ::Memory::WriteArray<BYTE>(callAddr, patch, 7);

	// 装后回读校验
	BYTE verify[7];
	PVZ::Memory::ReadArray<BYTE>(callAddr, verify, 7);
	if (memcmp(verify, patch, 7) != 0) return false;
	return true;
}

static bool InstallGarlicSmashSkipHook()
{
	bool a = PatchGarlicSmashCall(0x534BDC);   // 巨人遍历器 A 的 call
	bool b = PatchGarlicSmashCall(0x53502E);   // 巨人遍历器 B 的 call
	return (a || b);
}

// ---- 大蒜箭头贴图加载（UpArrow / DownArrow）----
static void GarlicLoadImages()
{
	__try
	{
		DWORD isNew = 0;
		Draw::PString variant = Draw::ToString("");
		Draw::PString fnUp = Draw::ToString("particles\\UpArrow.png");
		DWORD refUp = Draw::GetSharedImage(isNew, variant, fnUp);
		if (refUp != 0)
			g_garlicUpImage = Draw::SharedImageRefToImage(refUp);
		isNew = 0;
		Draw::PString fnDown = Draw::ToString("particles\\DownArrow.png");
		DWORD refDown = Draw::GetSharedImage(isNew, variant, fnDown);
		if (refDown != 0)
			g_garlicDownImage = Draw::SharedImageRefToImage(refDown);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_garlicArrowImgLoaded = false;
	}
}

// ---- 大蒜帧轮询：1阶血量阶梯 + 2阶方向表维护 ----
// ★ 血量口径（反汇编实证）：大蒜构造写 Hp=300（0x45DC52），但**进啃咬态时**写
//   Hp=MaxHp=0x190=400（0x45E23F），这才是实战值 ⇒ 0 阶上限 = 400 常量。
//   每帧把 [+0x44] 上限钉到目标值；上限被抬高的一瞬间把血回满（1 阶回满血）。
static void GarlicFrameInner(DWORD boardAddr)
{
	if (!CrashIsReadable(boardAddr, 0x100)) return;
	const DWORD PLANT_SIZE = 0x14C;
	int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
	int plantCount = MemSafeRead<int>(boardAddr + 0xB0);
	if (!plantArray || plantCount <= 0) return;

	g_garlicFrameTick++;
	int seen = 0, seen6 = 0;

	for (int i = 0; i < plantCount; i++)
	{
		DWORD p = (DWORD)(plantArray + i * PLANT_SIZE);
		if (MemSafeRead<BYTE>(p + 0x141)) continue;      // NotExist
		if (MemSafeRead<int>(p + 0x24) != (int)SeedType::Garlic) continue;
		seen++;

		int exp = 0;
		auto eit = g_plantExperience.find(p);
		if (eit != g_plantExperience.end()) exp = eit->second;
		int tier = GetPlantTier((int)SeedType::Garlic, exp);
		int row = MemSafeRead<int>(p + 0x1C);
		int rows = GarlicMapRows(boardAddr);
		if (rows == 6) seen6++;

		// ---- 1) 血量阶梯（T1 上限提升瞬间回满血）----
		int wantMax = (tier >= 1) ? g_garlicT1MaxHp : GARLIC_T0_MAXHP;
		int curMax = MemSafeRead<int>(p + 0x44);
		if (curMax != wantMax)
		{
			int hp = MemSafeRead<int>(p + 0x40);
			if (wantMax > curMax) hp = wantMax;      // 上调上限 → 回满血
			else if (hp > wantMax) hp = wantMax;     // 下调 → 封顶
			MemSafeWrite<int>(p + 0x44, wantMax);
			MemSafeWrite<int>(p + 0x40, hp);
		}

		// ---- 2) 2阶起建立方向槽位（初始=向上），并按本行约束钳制 ----
		if (tier >= 2)
		{
			int si = GarlicSlotEnsure(p);
			if (si != GARLIC_SLOT_NONE)
				g_garlic[si].dir = GarlicClampDir(boardAddr, row, g_garlic[si].dir);
		}

		g_garlicCurTier[p] = tier;
	}

	g_garlicCount6 = seen6;

	// ---- 3) 每 30 帧清理失效槽位（防内存池复用串档 + 槽位耗尽）----
	if ((g_garlicFrameTick % 30) == 0)
		GarlicPruneSlots(boardAddr);
}

static void GarlicFrame(DWORD boardAddr)
{
	__try
	{
		GarlicFrameInner(boardAddr);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ---- 大蒜箭头绘制（DrawUITop 层调用）----
// 画在大蒜右下角：格左上角 (25+col*80, 165+row*rowH) + 偏移；箭头 32x26。
// 箭头显示的是"被关卡行约束后的实际方向"（GarlicEffectiveDir）。
static void DrawGarlicArrows()
{
	if (g_garlicEnabled != 1) return;   // 0=停用 / 2=诊断模式（不画箭头）
	__try
	{
		DWORD g = (g_expPouchGStore != 0)
			? MemSafeRead<DWORD>(g_expPouchGStore) : 0;
		if (!g || !ExpPouchGraphicsValid(g)) return;

		int pvzBase = MemSafeRead<int>(0x6A9EC0);
		if (pvzBase < 0x400000) return;
		int boardAddr = MemSafeRead<int>(pvzBase + 0x768);
		if (!boardAddr) return;
		int gameMode = MemSafeRead<int>(pvzBase + 0x7F8);
		if (gameMode == 0x2B || gameMode == 0x32) return;

		// ★ 2026-10-16：这个条件在贴图缺失时会**每帧**调 GarlicLoadImages()，而每次
		//   Draw::ToString/GetSharedImage 都会漏 ≥1KB 堆内存（框架 AllocMemory 最小 1 页、
		//   调用方不回收）→ 堆几分钟内耗尽 → bad_alloc / ntdll 堆里 fault=0 的随机 AV。
		//   这段绘制路径在**选卡界面也会跑**，正好对上"选卡时随机崩"的现象。统一限流。
		if ((!g_garlicArrowImgLoaded || (!g_garlicUpImage && !g_garlicDownImage))
			&& ImageLoadRetryAllowed(8))
		{
			GarlicLoadImages();
			if (g_garlicUpImage || g_garlicDownImage)
				g_garlicArrowImgLoaded = true;
		}
		if (!g_garlicUpImage && !g_garlicDownImage) return;

		// 行高：五行 100px / 六行（泳池/迷雾）85px
		int scene = MemSafeRead<int>(boardAddr + 0x554C);
		int rowH = (scene == (int)SceneType::Pool || scene == (int)SceneType::Fog) ? 85 : 100;

		int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
		int plantCount = MemSafeRead<int>(boardAddr + 0xB0);
		if (!plantArray || plantCount <= 0) return;

		const DWORD PLANT_SIZE = 0x14C;
		for (int i = 0; i < plantCount; i++)
		{
			DWORD p = (DWORD)(plantArray + i * PLANT_SIZE);
			if (MemSafeRead<BYTE>(p + 0x141)) continue;   // NotExist
			if (MemSafeRead<int>(p + 0x24) != (int)SeedType::Garlic) continue;

			int exp = 0;
			auto eit = g_plantExperience.find(p);
			if (eit != g_plantExperience.end()) exp = eit->second;
			if (GetPlantTier((int)SeedType::Garlic, exp) < 2) continue;

			int row = MemSafeRead<int>(p + 0x1C);
			int col = MemSafeRead<int>(p + 0x28);
			if (row < 0 || row > 5 || col < 0 || col > 8) continue;

			int dir = GarlicEffectiveDir(boardAddr, p);
			DWORD img = (dir == GARLIC_UP) ? g_garlicUpImage : g_garlicDownImage;
			if (!img) img = (dir == GARLIC_UP) ? g_garlicDownImage : g_garlicUpImage;
			if (!img) continue;

			int px = 25 + col * 80 + g_garlicArrowOffX;
			int py = 165 + row * rowH + g_garlicArrowOffY;
			Draw::DrawImage(px, py, img, g);
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ---- 大蒜 2 阶：右击切换换行方向 ----
// 由右键沿检测分派调用。返回 1=已处理（大蒜），0=非大蒜。
// 语义（需求原文）：玩家手动指定换行方向（初始向上），右击切换；
//   箭头始终显示"被关卡行约束后的实际方向" ⇒ 即使该行被约束，切换也照常记录偏好，
//   只是当前显示/生效方向 = 钳制结果（例如五行第1行永远显示"下"）。
static int GarlicOnRightClick(DWORD plantAddr, DWORD boardAddr)
{
	if (!g_garlicEnabled) return 0;
	if (plantAddr < 0x10000 || !boardAddr) return 0;
	if (MemSafeRead<int>(plantAddr + 0x24) != (int)SeedType::Garlic) return 0;

	int exp = 0;
	auto eit = g_plantExperience.find(plantAddr);
	if (eit != g_plantExperience.end()) exp = eit->second;
	if (GetPlantTier((int)SeedType::Garlic, exp) < 2) return 1;   // 未到2阶：吃掉点击但不动作

	int si = GarlicSlotEnsure(plantAddr);
	if (si == GARLIC_SLOT_NONE) return 1;

	int cur = g_garlic[si].dir;
	int want = (cur == GARLIC_UP) ? GARLIC_DOWN : GARLIC_UP;
	int row = MemSafeRead<int>(plantAddr + 0x1C);
	int actual = GarlicClampDir(boardAddr, row, want);
	g_garlic[si].dir = actual;      // 换行决策与箭头都以它为唯一口径
	if (g_garlicDebug)
	{
		GARLIC_LOGP("[garlic] rclick row="); GARLIC_LOGN(row);
		GARLIC_LOGP(" want="); GARLIC_LOGN(want);
		GARLIC_LOGP(" actual="); GARLIC_LOGN(actual);
		GARLIC_LOGL("");
	}
	return 1;
}

// ---- 大蒜诊断汇总（GARLIC_DEBUG=1 时每次安装状态变化/换行各写一行）----
static void GarlicDebugReport(const char* tag)
{
	if (!g_garlicDebug) return;
	GARLIC_LOGP("[garlic] "); GARLIC_LOGP(tag);
	GARLIC_LOGP(" rowHook=");   GARLIC_LOGN(g_garlicRowHookState);
	GARLIC_LOGP(" smashHook="); GARLIC_LOGN(g_garlicSmashHookState);
	GARLIC_LOGP(" garlics=");   GARLIC_LOGN(g_garlicCount);
	GARLIC_LOGP(" sixRow=");    GARLIC_LOGN(g_garlicCount6);
	GARLIC_LOGP(" picks=");     GARLIC_LOGN(g_garlicPickCalls);
	GARLIC_LOGP(" writes=");    GARLIC_LOGN(g_garlicRowWrites);
	GARLIC_LOGP(" noTarget=");  GARLIC_LOGN(g_garlicNoTarget);
	GARLIC_LOGP(" eAddr=");     GARLIC_LOGN(g_garlicEarlyAddr);
	GARLIC_LOGP(" eRow=");      GARLIC_LOGN(g_garlicEarlyRow);
	GARLIC_LOGP(" eBoard=");    GARLIC_LOGN(g_garlicEarlyBoard);
	GARLIC_LOGP(" upImg=");     GARLIC_LOGN((int)g_garlicUpImage);
	GARLIC_LOGP(" downImg=");   GARLIC_LOGN((int)g_garlicDownImage);
	GARLIC_LOGL("");
}

// ==================== 大嘴花（Chomper）等阶机制：每帧轮询 ====================// 三项工作：①等阶血量上限阶梯写入 ②进入消化态(0xD)时把 +0x54(AttributeCountdown)
// 覆盖成配置的消化时间（plant_attack_speed.ini 秒→厘秒）③离开消化态时回血100。
// 实体含局部对象（Grep 不需容器，仍拆 Inner 包 __try 稳妥）。
static void ChomperFrameInner(DWORD boardAddr)
{
	if (!CrashIsReadable(boardAddr, 0x100)) return;
	const DWORD PLANT_SIZE = 0x14C;
	int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
	int plantCount = MemSafeRead<int>(boardAddr + 0xB0);
	if (!plantArray || plantCount <= 0) return;

	for (int i = 0; i < plantCount; i++)
	{
		DWORD p = (DWORD)(plantArray + i * PLANT_SIZE);
		if (MemSafeRead<BYTE>(p + 0x141)) continue;   // NotExist
		if (MemSafeRead<int>(p + 0x24) != (int)SeedType::Chomper) continue;

		int exp = 0;
		auto eit = g_plantExperience.find(p);
		if (eit != g_plantExperience.end()) exp = eit->second;
		int tier = GetPlantTier((int)SeedType::Chomper, exp);

		// ---- 1) 等阶血量上限阶梯 ----
		int wantMax = g_chomperMaxHpLadder[tier];
		int curMax = MemSafeRead<int>(p + 0x44);
		if (curMax != wantMax)
		{
			int hp = MemSafeRead<int>(p + 0x40);
			if (hp > wantMax) hp = wantMax;     // 上调上限时封顶；下调不削当前血
			MemSafeWrite<int>(p + 0x44, wantMax);
			MemSafeWrite<int>(p + 0x40, hp);
		}

		// ---- 2/3) 消化计时覆盖 + 消化完成回血（靠"进入/离开 0xD"状态迁移判定）----
		int state = MemSafeRead<int>(p + 0x3C);
		auto lit = g_chomberLastState.find(p);
		if (lit == g_chomberLastState.end())
		{
			g_chomberLastState[p] = state;      // 首次见到：只记基线，不触发
			continue;
		}
		int last = lit->second;
		if (state == 0xD && last != 0xD)
		{
			// 进入消化态：原生已写 +0x54=4000(40秒)，覆盖成配置消化时间
			int digestCs = (int)(GetPlantAttackSpeed((int)SeedType::Chomper, tier) * 100.0f + 0.5f);
			if (digestCs >= 1)
				MemSafeWrite<int>(p + 0x54, digestCs);
		}
		else if (last == 0xD && state != 0xD)
		{
			// 消化完成：回复 100 血（封顶 MaxHp）
			int hp = MemSafeRead<int>(p + 0x40);
			int max = MemSafeRead<int>(p + 0x44);
			hp += g_chomberDigestHeal;
			if (hp > max) hp = max;
			MemSafeWrite<int>(p + 0x40, hp);
		}
		lit->second = state;
	}
}

// __try 外壳（避开 C2712）
static void ChomperFrame(DWORD boardAddr)
{
	__try
	{
		ChomperFrameInner(boardAddr);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ==================== 磁力菇（MagnetShroom）等阶机制：实现 ====================
// ★hook 帧内铁律：只做指针读写 + POD 线性查找 + 经验表 find；禁 CRT 重活。
//   凡"发经验 / 索敌 / 结算伤害 / 生成表现"一律只登记事件，由 MagFrame 轮询帧执行。

// ---- 基础查询 ----
static int MagTierOf(DWORD plantAddr)
{
	int exp = 0;
	auto it = g_plantExperience.find((int)plantAddr);
	if (it != g_plantExperience.end()) exp = it->second;
	return GetPlantTier((int)SeedType::Magnetshroom, exp);
}
static bool MagIsMagnet(DWORD p)
{
	return p >= 0x10000
		&& MemSafeRead<int>(p + 0x24) == (int)SeedType::Magnetshroom
		&& !MemSafeRead<BYTE>(p + 0x141);
}
static int MagShieldIdx(int row, int col)
{
	for (int i = 0; i < g_magShieldCount; i++)
		if (g_magShield[i].row == row && g_magShield[i].col == col) return i;
	return -1;
}
static void MagShieldSet(int row, int col, int hp)
{
	int i = MagShieldIdx(row, col);
	if (i >= 0) { g_magShield[i].hp = hp; return; }
	if (g_magShieldCount >= 64) return;
	g_magShield[g_magShieldCount].row = row;
	g_magShield[g_magShieldCount].col = col;
	g_magShield[g_magShieldCount].hp = hp;
	g_magShieldCount++;
}
static void MagShieldEraseAt(int idx)
{
	if (idx < 0 || idx >= g_magShieldCount) return;
	g_magShield[idx] = g_magShield[g_magShieldCount - 1];
	g_magShieldCount--;
}
// 某植物所在格的护盾下标（-1 = 无盾）。行/列超界或地址非法一律返回 -1。
static int MagShieldIdxOfPlant(DWORD plantAddr)
{
	if (plantAddr < 0x10000) return -1;
	int row = MemSafeRead<int>(plantAddr + 0x1C);
	int col = MemSafeRead<int>(plantAddr + 0x28);
	if (row < 0 || row > 5 || col < 0 || col > 8) return -1;
	return MagShieldIdx(row, col);
}

// ---- 铁器贴图：直接读游戏已加载好的 Image* 全局 ----
// 权威来源：Plant::DrawMagnetItems @0x465460 的 21 路线性链（每类一个独立 Image* 全局，
// 不是数组）。这些全局都在 .data 零初始化区，运行时由
// Sexy::ExtractLoadingImagesResources @0x477F50 填入；资源未就绪时读到 0 →
// 本函数返回 0（不画飞行贴图，但伤害 / 经验 / 上盾照常）。
static DWORD MagItemImage(int itemType)
{
	DWORD slot = 0;
	switch (itemType)
	{
	case 1:  slot = 0x6A73B8; break;   // Pail_1            reanim\Zombie_bucket1.png
	case 2:  slot = 0x6A7AF8; break;   // Pail_2            reanim\Zombie_bucket2.png
	case 3:  slot = 0x6A7330; break;   // Pail_3            reanim\Zombie_bucket3.png
	case 4:  slot = 0x6A76F4; break;   // FootballHelmet_1  reanim\Zombie_football_helmet.png
	case 5:  slot = 0x6A737C; break;   // FootballHelmet_2  reanim\Zombie_football_helmet2.png
	case 6:  slot = 0x6A7A60; break;   // FootballHelmet_3  reanim\Zombie_football_helmet3.png
	case 7:  slot = 0x6A7398; break;   // Door_1            reanim\Zombie_screendoor1.png
	case 8:  slot = 0x6A77C8; break;   // Door_2            reanim\Zombie_screendoor2.png
	case 9:  slot = 0x6A7690; break;   // Door_3            reanim\Zombie_screendoor3.png
	// 10/11/12 跳跳杆：原版用 particles\ZombiePogo.png 的 3 列条带图（cel = type-10），
	// 而本项目的 Draw 封装没有"按 cel 绘制"的接口 → 借用跳跳杆残损单帧图近似（纯外观）
	case 10: case 11: case 12: slot = 0x6A78C4; break;
	case 13: slot = 0x6A7604; break;   // JackInTheBox      reanim\Zombie_jackbox_box.png
	case 14: slot = 0x6A76B0; break;   // Ladder_1          reanim\Zombie_ladder_1.png
	case 15: slot = 0x6A7624; break;   // Ladder_2          reanim\Zombie_ladder_1_damage1.png
	case 16: slot = 0x6A77CC; break;   // Ladder_3          reanim\Zombie_ladder_1_damage2.png
	case 17: slot = 0x6A75F0; break;   // LadderPlaced      reanim\Zombie_ladder_5.png
	case 21: slot = 0x6A73F0; break;   // Pickaxe           reanim\Zombie_digger_pickaxe.png
	default: return 0;
	}
	DWORD img = (DWORD)MemSafeRead<int>((int)slot);
	// 有效性守卫：Image* 必须是堆/数据段指针，且虚表在代码段（否则宁可不画）
	if (img < 0x10000 || img > 0x7FFFFFFF) return 0;
	DWORD vt = (DWORD)MemSafeRead<int>((int)img);
	if (vt < 0x400000 || vt > 0x900000) return 0;
	return img;
}

// ---- 事件登记（hook 帧调用：只写 POD）----
static void MagPushAbsorb(DWORD zombieAddr, DWORD plantAddr)
{
	if (zombieAddr < 0x10000 || plantAddr < 0x10000) return;
	int helmType   = MemSafeRead<int>(zombieAddr + 0xC4);
	int shieldType = MemSafeRead<int>(zombieAddr + 0xD8);
	int kind, maxHp, itemType;
	if (helmType == (int)HelmType::Bucket || helmType == (int)HelmType::FootballCap)
	{
		// 头盔：游戏只清 +0xC4/+0xD0，保留 +0xD4(MaxHealth)
		kind = 0;
		maxHp = MemSafeRead<int>(zombieAddr + 0xD4);
		itemType = (helmType == (int)HelmType::Bucket) ? 1 : 4;
	}
	else if (shieldType == (int)ShieldType::ScreenDoor || shieldType == (int)ShieldType::Ladder)
	{
		// 盾牌：游戏经 DetachShield 清 +0xD8/+0xDC，保留 +0xE0(MaxHealth)
		kind = 1;
		maxHp = MemSafeRead<int>(zombieAddr + 0xE0);
		itemType = (shieldType == (int)ShieldType::ScreenDoor) ? 7 : 14;
	}
	else
	{
		// 跳跳杆 / 玩偶匣 / 矿工镐：不作为防具、没有耐久 → 按 0 处理
		int ztype  = MemSafeRead<int>(zombieAddr + 0x24);
		int zstate = MemSafeRead<int>(zombieAddr + 0x28);
		if (ztype == (int)ZombieType::PogoZombie)         itemType = 10;
		else if (zstate == 0xF)                           itemType = 13;
		else if (ztype == (int)ZombieType::DiggerZombie)  itemType = 21;
		else return;                                  // 不认识的铁器 → 不登记
		kind = 2; maxHp = 0;
	}
	if (maxHp < 0) maxHp = 0;

	// 同一僵尸重复登记（理论上不会）→ 覆盖旧记录
	for (int i = 0; i < g_magAbsorbCount; i++)
		if (g_magAbsorb[i].zombie == zombieAddr) { g_magAbsorb[i] = g_magAbsorb[g_magAbsorbCount - 1]; g_magAbsorbCount--; break; }

	if (g_magAbsorbCount >= 128)
	{
		// 满了：丢掉最旧的已消化记录；没有则丢弃本次登记（不影响吸铁本身）
		int drop = -1;
		for (int i = 0; i < g_magAbsorbCount; i++)
			if (g_magAbsorb[i].digested) { drop = i; break; }
		if (drop < 0) return;
		g_magAbsorb[drop] = g_magAbsorb[g_magAbsorbCount - 1];
		g_magAbsorbCount--;
	}

	MagAbsorbRec& r = g_magAbsorb[g_magAbsorbCount++];
	r.zombie   = zombieAddr;
	r.zombieId = MemSafeRead<int>(zombieAddr + 0x158);
	r.magnet   = plantAddr;
	r.magnetId = MemSafeRead<int>(plantAddr + 0x148);
	r.row      = MemSafeRead<int>(plantAddr + 0x1C);
	r.kind     = kind;
	r.maxHp    = maxHp;
	r.itemType = itemType;
	r.digested = 0;
	r.expPaid  = 0;
}

static void MagPushDigest(DWORD plantAddr)
{
	if (plantAddr < 0x10000) return;
	if (g_magDigestQCount >= 16) return;
	MagDigestEvt& e = g_magDigestQ[g_magDigestQCount++];
	e.magnet   = plantAddr;
	e.magnetId = MemSafeRead<int>(plantAddr + 0x148);
	e.row      = MemSafeRead<int>(plantAddr + 0x1C);
	e.itemType = MemSafeRead<int>(plantAddr + 0xD8);   // MagnetItem[0].Type（0x461F07 才清零）
}

// ---- 2 阶吸铁半径加成（hook 帧调用）----
static int __cdecl MagRadiusBonus(DWORD zombieAddr, DWORD plantAddr)
{
	if (g_magRadiusBonus <= 0) return 0;
	if (plantAddr < 0x10000) return 0;
	if (MemSafeRead<int>(plantAddr + 0x24) != (int)SeedType::Magnetshroom) return 0;
	if (MagTierOf(plantAddr) < 2) return 0;
	return g_magRadiusBonus;
}

// ---- 护盾承伤：僵尸啃食（0x52FCF0 hook 调用）----
// 返回 1 = 护盾吸收了本次啃食（调用方跳过扣血）
static int __cdecl MagShieldAbsorbEat(DWORD plantAddr, DWORD zombieAddr)
{
	if (plantAddr < 0x10000) return 0;
	int idx = MagShieldIdxOfPlant(plantAddr);
	if (idx < 0) return 0;
	// 原版每次啃食固定 4 点（0x52FCF0: add dword [esi+0x40],-4）
	int dmg = 4;
	g_magShield[idx].hp -= dmg;
	if (g_magShield[idx].hp <= 0)
	{
		// 盾碎：本格护盾消失（本格所有植物一起失去保护）
		MagShieldEraseAt(idx);
	}
	return 1;
}

// ---- 护盾承伤：碾压 / 爆炸等秒杀（并入高坚果的统一入口）----
// 返回 1 = 消耗整个护盾抵挡一次秒杀，植物不死
// ★ 护盾是「格」级的：同一格多株植物（花盆上再种一株）共用。巨人砸格/车类碾压会让
//   游戏「逐株」调用秒杀，因此挡下第一株后必须让同格其余植物在本帧一并免疫，
//   否则第二株会被砸扁（护盾已经被消耗掉了）。
static int g_magKillBlock[6][9];      // 本帧已被护盾挡下秒杀的格（值 = 帧戳）
static int g_magFrameStamp = 1;

static int __cdecl MagShieldAbsorbKill(DWORD plantAddr)
{
	if (plantAddr < 0x10000) return 0;
	int row = MemSafeRead<int>(plantAddr + 0x1C);
	int col = MemSafeRead<int>(plantAddr + 0x28);
	if (row < 0 || row > 5 || col < 0 || col > 8) return 0;
	// 本帧这个格已经被护盾挡下一次 → 同格其余植物一并保护（不再重复消耗）
	if (g_magKillBlock[row][col] == g_magFrameStamp) return 1;
	int idx = MagShieldIdx(row, col);
	if (idx < 0) return 0;
	MagShieldEraseAt(idx);                       // 整个护盾归零（一个盾只能换一次秒杀）
	g_magKillBlock[row][col] = g_magFrameStamp;
	return 1;
}

// ---- 僵尸死亡结算：被磁力菇吸走的铁器耐久（要扣除的量）----
static int MagAbsorbedExpHelm(DWORD zombieAddr)
{
	int sum = 0;
	for (int i = 0; i < g_magAbsorbCount; i++)
		if (g_magAbsorb[i].zombie == zombieAddr && g_magAbsorb[i].kind == 0)
			sum += g_magAbsorb[i].maxHp;
	return sum;
}
static int MagAbsorbedExpShield(DWORD zombieAddr)
{
	int sum = 0;
	for (int i = 0; i < g_magAbsorbCount; i++)
		if (g_magAbsorb[i].zombie == zombieAddr && g_magAbsorb[i].kind == 1)
			sum += g_magAbsorb[i].maxHp;
	return sum;
}
static void MagForgetZombie(DWORD zombieAddr)
{
	// 已被吸走的铁器在僵尸死亡时已结算完毕 → 记录可以丢
	for (int i = 0; i < g_magAbsorbCount; )
	{
		if (g_magAbsorb[i].zombie == zombieAddr)
		{
			g_magAbsorb[i] = g_magAbsorb[g_magAbsorbCount - 1];
			g_magAbsorbCount--;
		}
		else i++;
	}
}
static void MagOnPlantShieldRemoved(DWORD plantAddr)
{
	// 植物被铲除/死亡：若它所在格已经空了，立刻撤掉该格护盾（不必等下一帧轮询）
	if (plantAddr < 0x10000) return;
	DWORD boardAddr = MemSafeRead<DWORD>(plantAddr + 4);
	if (!boardAddr) return;
	int row = MemSafeRead<int>(plantAddr + 0x1C);
	int col = MemSafeRead<int>(plantAddr + 0x28);
	if (row < 0 || row > 5 || col < 0 || col > 8) return;
	int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
	int plantCount = MemSafeRead<int>(boardAddr + 0xB0);
	if (!plantArray || plantCount <= 0) return;
	const DWORD PLANT_SIZE = 0x14C;
	for (int i = 0; i < plantCount; i++)
	{
		DWORD p = (DWORD)(plantArray + i * PLANT_SIZE);
		if (p == plantAddr) continue;
		if (MemSafeRead<BYTE>(p + 0x141)) continue;
		if (MemSafeRead<int>(p + 0x1C) != row) continue;
		if (MemSafeRead<int>(p + 0x28) != col) continue;
		return;                                  // 同格还有别的植物 → 护盾保留
	}
	MagShieldEraseAt(MagShieldIdx(row, col));
}

// ---- 本行扫格：返回每格「有植物 / 格内最低血量」----
static void MagScanRow(DWORD boardAddr, int row, int* hasPlant, int* minHp)
{
	for (int c = 0; c < 9; c++) { hasPlant[c] = 0; minHp[c] = 0; }
	int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
	int plantCount = MemSafeRead<int>(boardAddr + 0xB0);
	if (!plantArray || plantCount <= 0) return;
	const DWORD PLANT_SIZE = 0x14C;
	for (int i = 0; i < plantCount; i++)
	{
		DWORD p = (DWORD)(plantArray + i * PLANT_SIZE);
		if (MemSafeRead<BYTE>(p + 0x141)) continue;          // NotExist
		if (MemSafeRead<int>(p + 0x1C) != row) continue;
		int c = MemSafeRead<int>(p + 0x28);
		if (c < 0 || c > 8) continue;
		int hp = MemSafeRead<int>(p + 0x40);
		if (!hasPlant[c] || hp < minHp[c]) minHp[c] = hp;
		hasPlant[c] = 1;
	}
}

// 本行所有「有植物的格」是否都已有满耐久护盾（3 阶扔铁器的前置条件）
static int MagRowAllShieldsFull(DWORD boardAddr, int row)
{
	int hasPlant[9], minHp[9];
	MagScanRow(boardAddr, row, hasPlant, minHp);
	int any = 0;
	for (int c = 0; c < 9; c++)
	{
		if (!hasPlant[c]) continue;
		any = 1;
		int idx = MagShieldIdx(row, c);
		if (idx < 0 || g_magShield[idx].hp < g_magShieldHp) return 0;
	}
	return any;
}

// 1 阶护盾目标选择（返回列号，-1 = 什么也不做）
// 规则：① 无盾格优先 ② 都有盾时盾耐久最低的格重置满 ③ 全满 → 不做
//       同级：④ 格内植物最低血量低 ⑤ 离磁力菇近（磁力菇自己最近） ⑥ 靠右
static int MagPickShieldCell(DWORD boardAddr, int row, int magnetCol)
{
	int hasPlant[9], minHp[9];
	MagScanRow(boardAddr, row, hasPlant, minHp);

	int shieldHp[9];
	for (int c = 0; c < 9; c++) shieldHp[c] = -1;
	for (int i = 0; i < g_magShieldCount; i++)
		if (g_magShield[i].row == row && g_magShield[i].col >= 0 && g_magShield[i].col <= 8)
			shieldHp[g_magShield[i].col] = g_magShield[i].hp;

	int bestCol = -1, bestShielded = 0, bestSh = 0, bestHp = 0, bestDist = 0;
	for (int c = 0; c < 9; c++)
	{
		if (!hasPlant[c]) continue;
		int shielded = (shieldHp[c] >= 0) ? 1 : 0;
		if (shielded && shieldHp[c] >= g_magShieldHp) continue;   // 规则③：满耐久不参与
		int sh   = shielded ? shieldHp[c] : 0;
		int hp   = minHp[c];
		int dist = (c > magnetCol) ? (c - magnetCol) : (magnetCol - c);

		bool better;
		if (bestCol < 0)                       better = true;
		else if (shielded != bestShielded)     better = (shielded == 0);      // ① 无盾优先
		else if (shielded && sh != bestSh)     better = (sh < bestSh);        // ② 盾耐久低优先
		else if (hp != bestHp)                 better = (hp < bestHp);        // ④ 血低优先
		else if (dist != bestDist)             better = (dist < bestDist);    // ⑤ 近优先
		else                                   better = (c > bestCol);        // ⑥ 靠右
		if (better) { bestCol = c; bestShielded = shielded; bestSh = sh; bestHp = hp; bestDist = dist; }
	}
	return bestCol;
}

// ---- 3 阶索敌：全屏最近的「可索敌」敌人 ----
// 用游戏自带的 Zombie::EffectedByDamage(0x531A80) 判定，flags =
// DRF_GROUND|DRF_FLYING|DRF_SUBMERGED(7)：
//   · 地面僵尸 / 空中气球(FLYING) / 水中潜水(SUBMERGED) 可索敌
//   · 未出土矿工（state==0x20，需要 DRF_UNDERGROUND）排除
//   · 未低头僵王（僵王仅 0x56..0x5A 等低头相位可被索敌）排除
//   · 被魅惑僵尸、濒死僵尸、墓碑出土中([+0x64]==9)、蹦极/投石车等同样被排除
static int __cdecl MagCanTarget(DWORD zombieAddr)
{
	if (zombieAddr < 0x10000) return 0;
	volatile DWORD z = zombieAddr;      // volatile → 强制落栈，内联汇编里可直接当内存操作数
	volatile int  ok = 0;
	__asm
	{
		pushad
		push 7                              // theDamageRangeFlags
		mov  esi, z
		mov  eax, 0x531A80                  // Zombie::EffectedByDamage（ret 4 自清栈参数）
		call eax
		mov  ok, eax
		popad
	}
	return ok ? 1 : 0;
}

static DWORD MagFindThrowTarget(DWORD boardAddr, DWORD magnetAddr)
{
	if (!boardAddr || magnetAddr < 0x10000) return 0;
	int zArray = MemSafeRead<int>(boardAddr + 0x90);
	int zCount = MemSafeRead<int>(boardAddr + 0x94);
	if (!zArray || zCount <= 0) return 0;
	int mx   = MemSafeRead<int>(magnetAddr + 8);
	int mrow = MemSafeRead<int>(magnetAddr + 0x1C);
	const DWORD ZSIZE = 0x15C;
	DWORD best = 0; float bestD2 = 0.0f;
	for (int i = 0; i < zCount; i++)
	{
		DWORD z = (DWORD)(zArray + i * (int)ZSIZE);
		if (!MagCanTarget(z)) continue;
		float zx  = MemSafeRead<float>(z + 0x2C);
		float zy  = MemSafeRead<float>(z + 0x30);
		int   zrow = MemSafeRead<int>(z + 0x1C);
		float dx = zx - (float)mx;
		float dy = (float)(((zrow - mrow) * 80) + (int)(zy - (float)MemSafeRead<int>(magnetAddr + 0xC)));
		float d2 = dx * dx + dy * dy;
		if (!best || d2 < bestD2) { best = z; bestD2 = d2; }
	}
	return best;
}

// ---- 飞行铁器（纯表现）----
static void MagAddFly(DWORD magnetAddr, DWORD targetAddr, int itemType)
{
	int slot = -1;
	for (int i = 0; i < 16; i++) if (!g_magFly[i].active) { slot = i; break; }
	if (slot < 0) return;
	MagFly& f = g_magFly[slot];
	f.active   = 1;
	f.itemType = itemType;
	f.img      = MagItemImage(itemType);
	f.x0 = (float)MemSafeRead<int>(magnetAddr + 8);
	f.y0 = (float)MemSafeRead<int>(magnetAddr + 0xC);
	f.x1 = MemSafeRead<float>(targetAddr + 0x2C);
	f.y1 = MemSafeRead<float>(targetAddr + 0x30) - 40.0f;
	f.t   = 0;
	f.dur = (g_magThrowMs + 9) / 10;
	if (f.dur < 1)  f.dur = 1;
	if (f.dur > 35) f.dur = 35;                 // 上限 350ms
}

// ---- 上盾闪光（表现）----
// 同一格重复上盾只重置计时，不叠加；满了就顶掉最旧的一个。
static void MagPushShieldFx(int row, int col)
{
	for (int i = 0; i < g_magShieldFxCount; i++)
		if (g_magShieldFx[i].row == row && g_magShieldFx[i].col == col)
		{
			g_magShieldFx[i].t = 0;
			return;
		}
	if (g_magShieldFxCount >= 8)
	{
		int oldest = 0;
		for (int i = 1; i < g_magShieldFxCount; i++)
			if (g_magShieldFx[i].t > g_magShieldFx[oldest].t) oldest = i;
		g_magShieldFx[oldest].row = row;
		g_magShieldFx[oldest].col = col;
		g_magShieldFx[oldest].t = 0;
		return;
	}
	g_magShieldFx[g_magShieldFxCount].row = row;
	g_magShieldFx[g_magShieldFxCount].col = col;
	g_magShieldFx[g_magShieldFxCount].t = 0;
	g_magShieldFxCount++;
}

// ---- 3 阶：扔铁器（轮询帧执行）----
// 返回 1 = 已扔出（或无需持有）；0 = 场上没有可索敌敌人 → 继续持有
static int MagTryThrow(DWORD boardAddr, DWORD magnetAddr, int itemType)
{
	DWORD target = MagFindThrowTarget(boardAddr, magnetAddr);
	if (!target) return 0;
	PVZ::Zombie z((int)target);
	if (z.isValid())
		z.Hit(g_magThrowDamage, PVZ::DAMAGEF_NONE);
	MagAddFly(magnetAddr, target, itemType);
	// 命中点播原版特效 0x0F「锤子：锤僵尸」（particles\Pow.xml）。
	// 与击退弹命中用的是同一条成熟通道（SeaBurstSpawnParticle），偏移也沿用同一对常量。
	// ★ 本函数只在每帧轮询帧（MagFrame）里被调用，不是 hook 帧 → 可以直接生成粒子。
	SeaBurstSpawnParticle(z.X + KB_POW_FX_DX, z.Y + KB_POW_FX_DY, KB_POW_FX_ID);
	return 1;
}

static void MagPushHeld(DWORD magnetAddr, int row, int itemType, int kind, int maxHp)
{
	for (int i = 0; i < g_magHeldCount; i++)
		if (g_magHeld[i].magnet == magnetAddr) { g_magHeld[i].itemType = itemType; g_magHeld[i].maxHp = maxHp; return; }
	if (g_magHeldCount >= 32) return;
	MagHeld& h = g_magHeld[g_magHeldCount++];
	h.magnet   = magnetAddr;
	h.magnetId = MemSafeRead<int>(magnetAddr + 0x148);
	h.row      = row;
	h.itemType = itemType;
	h.kind     = kind;
	h.maxHp    = maxHp;
}

// ---- 消化完成处理（轮询帧执行：发经验 + 上盾 / 扔铁器）----
static void MagProcessDigest(DWORD boardAddr, const MagDigestEvt& e)
{
	DWORD magnet = e.magnet;
	if (magnet < 0x10000) return;
	// 1) 找到这次吸的铁器记录（没有 → 地上梯子等特殊来源）
	int recIdx = -1;
	for (int i = 0; i < g_magAbsorbCount; i++)
		if (g_magAbsorb[i].magnet == magnet && !g_magAbsorb[i].digested) { recIdx = i; break; }

	int gain     = 0;
	int kind     = 2;
	int itemType = e.itemType;                     // ★ 优先用游戏写在 [plant+0xD8] 的真实档位
	if (recIdx >= 0)
	{
		gain     = g_magAbsorb[recIdx].maxHp;
		kind     = g_magAbsorb[recIdx].kind;
		if (itemType == 0) itemType = g_magAbsorb[recIdx].itemType;   // 兜底：登记时的基础档
		g_magAbsorb[recIdx].digested = 1;
	}
	else if (itemType == 0x11)                     // LadderPlaced：架在草坪上的梯子
	{
		gain = g_magLadderHp;
		kind = 1;                                  // 视作盾牌类，不参与僵尸死亡扣除（无僵尸）
	}

	// 2) 经验：等于该铁器的满耐久
	if (gain > 0 && MagIsMagnet(magnet))
	{
		AddPlantExperience(magnet, gain);
		if (recIdx >= 0) g_magAbsorb[recIdx].expPaid = 1;
	}

	int tier = MagTierOf(magnet);
	if (tier < 1) return;                          // 0 阶同原版

	int row = e.row;
	if (row < 0 || row > 5) return;
	int magnetCol = MemSafeRead<int>(magnet + 0x28);

	// 3) 3 阶：本行所有格护盾都满耐久 → 扔铁器（没目标就一直持有）
	if (tier >= 3 && MagRowAllShieldsFull(boardAddr, row))
	{
		if (MagTryThrow(boardAddr, magnet, itemType)) return;
		MagPushHeld(magnet, row, itemType, kind, gain);
		return;
	}

	// 4) 1 阶+：给本行一格上 / 重置护盾
	int col = MagPickShieldCell(boardAddr, row, magnetCol);
	if (col >= 0)
	{
		MagShieldSet(row, col, g_magShieldHp);
		MagPushShieldFx(row, col);       // 表现：在该格播「坚果圣盾」并淡出
		}
	// col < 0（本行护盾全满）→ 什么都不做
}

// ---- 每帧轮询（重活都在这里；hook 帧只登记）----
static void MagFrameInner(DWORD boardAddr)
{
	if (!CrashIsReadable(boardAddr, 0x100)) return;

	// 0) 新的一帧：清掉"本帧已被护盾挡下秒杀的格"标记
	g_magFrameStamp++;
	if (g_magFrameStamp <= 0) g_magFrameStamp = 1;      // 防溢出（int 回绕）
	for (int r = 0; r < 6; r++)
		for (int c = 0; c < 9; c++)
			g_magKillBlock[r][c] = 0;

	// 1) 消化完成事件（hook 帧登记，这里结算）
	while (g_magDigestQCount > 0)
	{
		MagDigestEvt e = g_magDigestQ[0];
		g_magDigestQ[0] = g_magDigestQ[--g_magDigestQCount];
		if (e.magnetId != MemSafeRead<int>(e.magnet + 0x148)) continue;   // 地址复用 → 丢弃
		MagProcessDigest(boardAddr, e);
	}

	// 2) 持有中的铁器：一有可索敌敌人就扔
	for (int i = 0; i < g_magHeldCount; )
	{
		MagHeld& h = g_magHeld[i];
		if (!MagIsMagnet(h.magnet) || h.magnetId != MemSafeRead<int>(h.magnet + 0x148)
			|| MemSafeRead<BYTE>(h.magnet + 0x141))
		{
			g_magHeld[i] = g_magHeld[--g_magHeldCount];      // 磁力菇没了 → 铁器丢失
			continue;
		}
		if (MagTryThrow(boardAddr, h.magnet, h.itemType))
		{
			g_magHeld[i] = g_magHeld[--g_magHeldCount];
			continue;
		}
		i++;
	}

	// 3) 飞行铁器推进
	for (int i = 0; i < 16; i++)
	{
		if (!g_magFly[i].active) continue;
		g_magFly[i].t++;
		if (g_magFly[i].t >= g_magFly[i].dur) g_magFly[i].active = 0;
	}

	// 3b) 上盾闪光推进（5 档 alpha × 每档 8 帧，走完即消失）
	for (int i = 0; i < g_magShieldFxCount; )
	{
		g_magShieldFx[i].t++;
		if (g_magShieldFx[i].t >= MAG_SHIELD_FX_STEPS * MAG_SHIELD_FX_FRAMES)
		{
			g_magShieldFx[i] = g_magShieldFx[--g_magShieldFxCount];
			continue;
		}
		i++;
	}

	// 4) 清理：空格的护盾、僵尸已消失的铁器记录
	// ★ 先一次性扫出「有植物的格」（6 行 × 9 列位图），再逐盾比对 —— 避免逐盾重扫植物数组
	{
		DWORD occupied[6] = { 0, 0, 0, 0, 0, 0 };
		int plantArray = MemSafeRead<int>(boardAddr + 0xAC);
		int plantCount = MemSafeRead<int>(boardAddr + 0xB0);
		const DWORD PLANT_SIZE = 0x14C;
		for (int i = 0; plantArray && i < plantCount; i++)
		{
			DWORD p = (DWORD)(plantArray + i * PLANT_SIZE);
			if (MemSafeRead<BYTE>(p + 0x141)) continue;
			int r = MemSafeRead<int>(p + 0x1C);
			int c = MemSafeRead<int>(p + 0x28);
			if (r < 0 || r > 5 || c < 0 || c > 8) continue;
			occupied[r] |= (1u << c);
		}
		for (int i = 0; i < g_magShieldCount; )
		{
			int r = g_magShield[i].row, c = g_magShield[i].col;
			if (r < 0 || r > 5 || c < 0 || c > 8 || !(occupied[r] & (1u << c)))
			{
				MagShieldEraseAt(i);
				continue;
			}
			i++;
		}
	}
	for (int i = 0; i < g_magAbsorbCount; )
	{
		DWORD z = g_magAbsorb[i].zombie;
		bool gone = (z < 0x10000) || MemSafeRead<BYTE>(z + 0xEC)
			|| (g_magAbsorb[i].zombieId != MemSafeRead<int>(z + 0x158));
		if (!gone && !g_magAbsorb[i].digested)
		{
			// 磁力菇中途没了 → 这份铁器作废（经验不发，但死亡结算依旧要扣）
			DWORD m = g_magAbsorb[i].magnet;
			if (m < 0x10000 || MemSafeRead<BYTE>(m + 0x141)
				|| g_magAbsorb[i].magnetId != MemSafeRead<int>(m + 0x148))
				g_magAbsorb[i].digested = 1;
		}
		if (gone) { g_magAbsorb[i] = g_magAbsorb[--g_magAbsorbCount]; continue; }
		i++;
	}

}
static void MagFrame(DWORD boardAddr)
{
	__try { MagFrameInner(boardAddr); }
	__except (EXCEPTION_EXECUTE_HANDLER) { }
}

// ---- 护盾 / 上盾闪光 / 飞行铁器绘制（DrawUITop 层；与大蒜箭头同款做法）----
// 加载 images\ 下的一张 PNG（失败返回 0）。GetSharedImage 自带按文件名缓存，重复调用很便宜。
static DWORD MagLoadOneImage(const char* path)
{
	DWORD img = 0;
	__try
	{
		DWORD isNew = 0;
		Draw::PString variant = Draw::ToString("");
		Draw::PString fn = Draw::ToString(path);
		DWORD ref = Draw::GetSharedImage(isNew, variant, fn);
		if (ref != 0) img = Draw::SharedImageRefToImage(ref);
	}
	__except (EXCEPTION_EXECUTE_HANDLER) { img = 0; }
	return img;
}

// 幂等：已加载的项直接跳过；未加载的下次绘制时再试（资源未就绪时不会卡死）
static void MagLoadShieldImage()
{
	__try
	{
		if (!g_magShieldImg)
			g_magShieldImg = MagLoadOneImage("images\\PlantShield.png");
		if (!g_magShieldFxImg[0])
		{
			g_magShieldFxImg[0] = MagLoadOneImage("images\\PlantShield_fx100.png");
			g_magShieldFxImg[1] = MagLoadOneImage("images\\PlantShield_fx80.png");
			g_magShieldFxImg[2] = MagLoadOneImage("images\\PlantShield_fx60.png");
			g_magShieldFxImg[3] = MagLoadOneImage("images\\PlantShield_fx40.png");
			g_magShieldFxImg[4] = MagLoadOneImage("images\\PlantShield_fx20.png");
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER) { }
}

static void DrawMagnetShields()
{
	__try
	{
		DWORD g = (g_expPouchGStore != 0) ? MemSafeRead<DWORD>(g_expPouchGStore) : 0;
		if (!g || !ExpPouchGraphicsValid(g)) return;

		int pvzBase = MemSafeRead<int>(0x6A9EC0);
		if (pvzBase < 0x400000) return;
		int boardAddr = MemSafeRead<int>(pvzBase + 0x768);
		if (!boardAddr) return;
		int gameMode = MemSafeRead<int>(pvzBase + 0x7F8);
		if (gameMode == 0x2B || gameMode == 0x32) return;      // 禅境花园/智慧树不画

		// ★★★ 2026-10-16 关键修复：MagLoadShieldImage 每次尝试最多 6 张图，
		//   而每张图 = ToString("") + ToString(path) + GetSharedImage ≈ 3.1KB 堆泄漏
		//   （框架 AllocMemory 最小 1 页 = 1024B，且调用方从不回收）⇒ 最坏 ~19KB/次。
		//   它原来在**绘制路径里每帧无条件调用**，而 onDrawUITop 在**选卡界面也会跑**
		//   ⇒ 只要缺任意一张 png，就能以 ~1MB/s 漏堆，32 位进程 2GB 用户空间几十分钟耗尽。
		//   耗尽后的表现与 D:\pvz_crash.log 完全吻合：
		//     · code=0xE06D7363（std::bad_alloc：operator new 失败被抛）
		//     · code=0xC0000005 且 **fault=0**、EIP 落在 ntdll 堆函数里（堆提交失败/错误处理踩 NULL）
		//   现在统一限流：最多 600 次尝试，之后永久放弃（图像真缺失时不再空转漏堆）。
		if (ImageLoadRetryAllowed(9))
			MagLoadShieldImage();

		int scene = MemSafeRead<int>(boardAddr + 0x554C);
		int rowH = (scene == (int)SceneType::Pool || scene == (int)SceneType::Fog) ? 85 : 100;

		// ① 护盾：每格画一张（同格多株共用一张）。偏移已定稿 → 硬编码常量。
		if (g_magShieldImg)
		{
			for (int i = 0; i < g_magShieldCount; i++)
			{
				int row = g_magShield[i].row, col = g_magShield[i].col;
				if (row < 0 || row > 5 || col < 0 || col > 8) continue;
				int px = 25 + col * 80 + MAG_SHIELD_OFF_X;
				int py = 165 + row * rowH + MAG_SHIELD_OFF_Y;
				Draw::DrawImage(px, py, g_magShieldImg, g);
			}
		}

		// ② 上盾闪光：在被上盾那一格播「坚果圣盾」，5 档预烘焙 alpha 逐档淡出。
		//    偏移由护盾偏移反推（两者可见中心重合），所以闪光一定落在护盾正中。
		for (int i = 0; i < g_magShieldFxCount; i++)
		{
			int row = g_magShieldFx[i].row, col = g_magShieldFx[i].col;
			if (row < 0 || row > 5 || col < 0 || col > 8) continue;
			int step = g_magShieldFx[i].t / MAG_SHIELD_FX_FRAMES;
			if (step < 0) step = 0;
			if (step >= MAG_SHIELD_FX_STEPS) step = MAG_SHIELD_FX_STEPS - 1;
			DWORD img = g_magShieldFxImg[step];
			if (!img) continue;
			int px = 25 + col * 80 + MAG_SHIELD_FX_OFF_X;
			int py = 165 + row * rowH + MAG_SHIELD_FX_OFF_Y;
			Draw::DrawImage(px, py, img, g);
		}

		// ③ 飞行中的铁器：加速飞行（位置 = 起终点线性插值，进度取 t²）
		for (int i = 0; i < 16; i++)
		{
			MagFly& f = g_magFly[i];
			if (!f.active || !f.img) continue;
			float p = (f.dur > 0) ? ((float)f.t / (float)f.dur) : 1.0f;
			if (p < 0.0f) p = 0.0f; if (p > 1.0f) p = 1.0f;
			float k = p * p;                                  // 加速（初速 0，末速最快）
			float x = f.x0 + (f.x1 - f.x0) * k;
			float y = f.y0 + (f.y1 - f.y0) * k;
			Draw::DrawImage((int)x, (int)y, f.img, g);
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER) { }
}

// ---- hook 安装 ----
// ① 吸到铁器 @0x461610（Plant::MagnetShroomAttactItem 入口）
//    入口 7 字节 = 51 (push ecx) + D9 05 88 93 67 00 (fld dword [0x679388])，
//    5 字节 E9 后剩 2 字节必须补 NOP。ebx=僵尸，栈参 [esp+4]=植物。
static bool InstallMagAbsorbHook()
{
	DWORD hookAddr = 0x461610;
	static const BYTE kExpected[7] = { 0x51, 0xD9, 0x05, 0x88, 0x93, 0x67, 0x00 };
	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 7);
	if (memcmp(raw, kExpected, 7) != 0) return false;

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0) return false;

	BYTE tp[64]; int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD t) { tp[p++] = 0xE8; put32((int)((DWORD)t - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp  = [&](DWORD t) { tp[p++] = 0xE9; put32((int)((DWORD)t - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                        // pushad
	tp[p++] = 0xFF; tp[p++] = 0x74; tp[p++] = 0x24; tp[p++] = 0x24; // push [esp+0x24] 植物(栈参)
	tp[p++] = 0x53;                                        // push ebx 僵尸
	putRelCall((DWORD)&MagPushAbsorb);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x08;        // add esp,8
	tp[p++] = 0x61;                                        // popad
	tp[p++] = 0x51;                                        // push ecx（原指令）
	tp[p++] = 0xD9; tp[p++] = 0x05; tp[p++] = 0x88; tp[p++] = 0x93; tp[p++] = 0x67; tp[p++] = 0x00; // fld dword [0x679388]
	putRelJmp(hookAddr + 7);

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	MemSafeWrite<BYTE>(hookAddr + 5, 0x90);                // 补 2 字节 NOP
	MemSafeWrite<BYTE>(hookAddr + 6, 0x90);
	BYTE verify[7];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, verify, 7);
	return (verify[0] == 0xE9 && verify[5] == 0x90 && verify[6] == 0x90);
}

// ② 消化完成 @0x461E3C（UpdateMagnetShroom 内 State==0x1B 且 +0x54==0 的唯一落点）
//    原 6 字节 = D9 05 74 96 67 00 (fld dword [0x679674])；5 字节 E9 后补 1 字节 NOP。
//    ebx=植物；此刻 [ebx+0xD8]=MagnetItem[0].Type 仍有效（0x461F07 才清零）。
static bool InstallMagDigestHook()
{
	DWORD hookAddr = 0x461E3C;
	static const BYTE kExpected[6] = { 0xD9, 0x05, 0x74, 0x96, 0x67, 0x00 };
	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 6);
	if (memcmp(raw, kExpected, 6) != 0) return false;

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0) return false;

	BYTE tp[64]; int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD t) { tp[p++] = 0xE8; put32((int)((DWORD)t - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp  = [&](DWORD t) { tp[p++] = 0xE9; put32((int)((DWORD)t - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                        // pushad
	tp[p++] = 0x53;                                        // push ebx 植物
	putRelCall((DWORD)&MagPushDigest);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;        // add esp,4
	tp[p++] = 0x61;                                        // popad
	tp[p++] = 0xD9; tp[p++] = 0x05; tp[p++] = 0x74; tp[p++] = 0x96; tp[p++] = 0x67; tp[p++] = 0x00; // fld dword [0x679674]
	putRelJmp(hookAddr + 6);

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	MemSafeWrite<BYTE>(hookAddr + 5, 0x90);
	BYTE verify[6];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, verify, 6);
	return (verify[0] == 0xE9 && verify[5] == 0x90);
}

// ③ 2 阶吸铁半径 +90 @0x4620F4（16 字节整段无外部跳入，可整体替换）
//    原 16 字节：cmp byte [ebx+0x51],0 / mov eax,0x10E / je +5 / mov eax,0x140
//    ebx=僵尸、edi=植物；替换后由跳板复刻原段再 add eax,加成。
static bool InstallMagRadiusHook()
{
	DWORD hookAddr = 0x4620F4;
	static const BYTE kExpected[16] = {
		0x80, 0x7B, 0x51, 0x00,                          // cmp byte [ebx+0x51],0
		0xB8, 0x0E, 0x01, 0x00, 0x00,                    // mov eax,0x10E (270)
		0x74, 0x05,                                      // je +5
		0xB8, 0x40, 0x01, 0x00, 0x00                     // mov eax,0x140 (320)
	};
	BYTE raw[20];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 16);
	if (memcmp(raw, kExpected, 16) != 0) return false;

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0) return false;

	BYTE tp[96]; int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD t) { tp[p++] = 0xE8; put32((int)((DWORD)t - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp  = [&](DWORD t) { tp[p++] = 0xE9; put32((int)((DWORD)t - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                        // pushad
	tp[p++] = 0x53;                                        // push ebx 僵尸
	tp[p++] = 0x57;                                        // push edi 植物
	putRelCall((DWORD)&MagRadiusBonus);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x08;        // add esp,8
	tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x1C; // mov [esp+0x1C],eax（pushad 帧 EAX 槽）
	tp[p++] = 0x61;                                        // popad → eax = 加成
	tp[p++] = 0x8B; tp[p++] = 0xC8;                        // mov ecx,eax（暂存加成；0x462104 起自会重设 ecx）
	// ---- 原 16 字节（je 的相对偏移在原样复刻后依然正确）----
	for (int i = 0; i < 16; i++) tp[p++] = kExpected[i];
	tp[p++] = 0x03; tp[p++] = 0xC1;                        // add eax,ecx
	putRelJmp(0x462104);

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	for (int i = 5; i < 16; i++) MemSafeWrite<BYTE>(hookAddr + i, 0x90);   // 余下 11 字节 NOP
	BYTE verify[16];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, verify, 16);
	for (int i = 5; i < 16; i++) if (verify[i] != 0x90) return false;
	return (verify[0] == 0xE9);
}

// ④ 僵尸啃食先扣护盾 @0x52FCF0（Plant::TakeEatDamage）
//    原 7 字节 = 83 46 40 FC (add dword [esi+0x40],-4) + 8B 4E 40 (mov ecx,[esi+0x40])
//    esi=植物、ebp=僵尸。0x52 区运行时才解密 → 每帧重试、逐字节核对、超窗放弃。
static bool InstallMagEatHook()
{
	DWORD hookAddr = 0x52FCF0;
	static const BYTE kExpected[7] = { 0x83, 0x46, 0x40, 0xFC, 0x8B, 0x4E, 0x40 };
	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 7);
	if (memcmp(raw, kExpected, 7) != 0) return false;

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0) return false;

	BYTE tp[64]; int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD t) { tp[p++] = 0xE8; put32((int)((DWORD)t - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp  = [&](DWORD t) { tp[p++] = 0xE9; put32((int)((DWORD)t - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                        // pushad
	tp[p++] = 0x55;                                        // push ebp 僵尸
	tp[p++] = 0x56;                                        // push esi 植物
	putRelCall((DWORD)&MagShieldAbsorbEat);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x08;        // add esp,8
	tp[p++] = 0x85; tp[p++] = 0xC0;                        // test eax,eax
	tp[p++] = 0x61;                                        // popad（不破坏 flags）
	int jnzAt = p;
	tp[p++] = 0x75; tp[p++] = 0x00;                        // jnz BLOCKED（回填）
	// ---- ORIG：原 7 字节 ----
	tp[p++] = 0x83; tp[p++] = 0x46; tp[p++] = 0x40; tp[p++] = 0xFC;
	tp[p++] = 0x8B; tp[p++] = 0x4E; tp[p++] = 0x40;
	putRelJmp(0x52FCF7);
	// ---- BLOCKED：跳过扣血，但仍要加载 ecx（后续 IZ 分支会用它写回 [esi+0x40]）----
	*(BYTE*)(tp + jnzAt + 1) = (BYTE)(p - (jnzAt + 2));
	tp[p++] = 0x8B; tp[p++] = 0x4E; tp[p++] = 0x40;
	putRelJmp(0x52FCF7);

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	MemSafeWrite<BYTE>(hookAddr + 5, 0x90);
	MemSafeWrite<BYTE>(hookAddr + 6, 0x90);
	BYTE verify[7];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, verify, 7);
	return (verify[0] == 0xE9 && verify[5] == 0x90 && verify[6] == 0x90);
}

// 安装总入口（每帧轮询里调用；装不上只记一行，不刷日志）
static void MagInstallHooks()
{
	if (!g_magAbsorbHookInstalled) g_magAbsorbHookInstalled = InstallMagAbsorbHook();
	if (!g_magDigestHookInstalled) g_magDigestHookInstalled = InstallMagDigestHook();
	if (!g_magRadiusHookInstalled) g_magRadiusHookInstalled = InstallMagRadiusHook();
	if (!g_magEatHookInstalled && !g_magEatHookGivenUp)
	{
		if (InstallMagEatHook()) g_magEatHookInstalled = true;
		else if (++g_magEatHookTries > 600) g_magEatHookGivenUp = true;
	}
}

// ==================== 每帧主循环：__try 外壳 ====================
// onGameObjectsUpdate 是整个 mod 最大的每帧入口：三线射手 / 玉米投手 / 海蘑菇剧毒 /
// 防爆门 / 撑杆司令 / 金盏花 / 裂荚 / 卷心菜 等全部轮询逻辑都在这里，且大量读写
// 游戏对象地址（植物/僵尸/子弹/Board）。任何一处野指针、陈旧地址、内存池复用都会
// 直接把游戏带崩，且崩溃点往往落在 hook trampoline 或 DLL 里某个不相关的位置，
// 事后完全无法反查 —— 这正是"无故崩溃"难修的根因。
// 这里加一层 __try：异常发生时先由 CrashSwallowFilter 落盘完整现场（异常码/地址/
// 模块+RVA/寄存器/栈回溯/最后执行步骤），再吞掉异常 → 只跳过"这一帧"的轮询工作，
// 游戏继续跑（机制可能丢一帧，但不会崩）。
// ★ 外壳函数不能有任何需要析构的局部对象（MSVC C2712），故实体全部在 Inner。
static void onGameObjectsUpdateInner(DWORD boardAddress);   // 前向声明（实体在下方）

// ==================== 寒冰菇等阶：轮询帧执行（冻结 + 伤害 + 冰法阵）====================
// 消费 onPlantRemove 登记的爆炸请求，做四件事（分工同步于顶部数据结构注释）：
//   ① 冻结全屏僵尸（0/1阶=原版400cs，2/3阶=g_iceFreezeCs）+ 1阶以上单体 HitBody(80)
//   ② 登记"冻结时长再断言"（g_iceGrace，短期内每帧强制刷新），碾压原版可能晚到的 400cs
//   ③ 3阶在寒冰菇位置生成 3×3 冰法阵：路灯花灯光特效（0x2E）染浅蓝、叠放一次标注，
//      法阵到期（按 ms 时钟）时对持有句柄逐一 Die，保证光圈随消失不残留
//   ④ 每帧把处于法阵内的僵尸标记进 g_iceVulnZombies（脆弱增伤）并对其 Decelerate。
// 本函数含 std::vector 局部对象（GetAllZombies）→ __try 不能直接包裹（C2712），
// 由外层 IceFieldFrame 兜底。

// 移除一个路灯光粒子系统（0x5160C0 = TodParticleSystem::Die，压栈 this，被调方清栈）
static DWORD g_iceDiePsys = 0;
static void IceParticleDie(DWORD psysAddr)
{
	if (!psysAddr || psysAddr < 0x10000) return;
	g_iceDiePsys = psysAddr;
	__asm
	{
		pushad
		push g_iceDiePsys
		mov eax, 0x5160C0
		call eax            ; stdcall：被调方清栈，勿 add esp
		popad
	}
}

static void IceFieldFrameInner(DWORD boardAddr)
{
	if (!CrashIsReadable(boardAddr, 0x100)) return;
	DWORD now = GetTickCount();

	PVZ::Board board(boardAddr);
	auto zombies = board.GetAllZombies();

	// ---- ① 消费爆炸请求：冻结 + 伤害 + 法阵生成 ----
	if (g_iceBoomReqCount > 0)
	{
		for (int q = 0; q < g_iceBoomReqCount; q++)
		{
			int tier = g_iceBoomReqs[q].tier;
			int row  = g_iceBoomReqs[q].row;
			int col  = g_iceBoomReqs[q].col;
			int freezeCs = (tier >= 2) ? g_iceFreezeCs : ICE_FREEZE_DEFAULT_CS;
			IceLog("boom consumed: tier=%d row=%d col=%d freezeCs=%d zombies=%d fields=%d",
				tier, row, col, freezeCs, (int)zombies.size(), g_iceFieldCount);

			// 冻结全屏可冻结僵尸；1阶以上命中瞬间吃 80 直伤（无视护甲）
			for (auto& z : zombies)
			{
				if (!z.isValid() || z.NotExist) continue;
				z.Froze(freezeCs);
				if (tier >= 1 && z.canFroze())
					z.HitBody(ICE_T1_DAMAGE);
			}

			// ③ 3阶：以寒冰菇所在格为中心生成长时冰法阵（路灯花光晕贴图换淡蓝高不透明版）
			if (tier >= 3 && g_iceFieldCount < 16)
			{
				if (!g_iceFieldImageLoaded && ImageLoadRetryAllowed(6))
				{
					g_iceFieldImageLoaded = true;
					LoadIceFieldImage();
				}
				int cx = board.GridToXPixel(row, col);
				int cy = board.GridToYPixel(row, col);
				IceFieldRec& f = g_iceFields[g_iceFieldCount];
				f.cx = (float)cx;
				f.cy = (float)cy;
				f.row = row;       // 3×3 行判定基准（Row 字段精确判定，2026-09-13 修漏判）
				f.accumMs = 0;
				f.lastReal = now;
				f.psysCount = 0;
				g_iceFieldCount++;
				// 贴图位置：光晕贴图中心相对格子中心偏移（否则偏左上）+ 换淡蓝高不透明光晕贴图。
				// 视觉特效坐标 = 格子中心 + 偏移；句柄+槽位 Id 存 psys[]/psysId[]，
				// 法阵到期时校验 Id 后逐一 Die 移除（Id 变了=槽已被游戏回收复用，跳过防写坏堆）。
				float fx = (float)cx + ICE_FIELD_DX;
				float fy = (float)cy + ICE_FIELD_DY;
				for (int s = 0; s < 2; s++)
				{
					DWORD psys = SeaBurstSpawnParticle(fx, fy, ICE_FIELD_EFFECT);
					if (!psys || psys < 0x10000)
					{
						IceLog("boom tier=%d row=%d col=%d spawn%d FAIL psys=0x%X", tier, row, col, s, psys);
						continue;
					}
					// 换淡蓝高不透明光晕贴图（不再乘色染色）
					if (g_iceFieldImage)
						SeaBurstOverrideImage(psys, g_iceFieldImage);
					if (f.psysCount < 2)
					{
						DWORD sid = 0;
						if (CrashIsReadable(psys, 0x30))
							sid = MemSafeRead<DWORD>(psys + 0x28);   // 槽位 Id（0x518B90 实锤：Id=(世代<<16)|slot 写在 +0x28；★+0x9C 是动画池偏移，对 0x2C 槽是越界垃圾）
						f.psys[f.psysCount] = psys;
						f.psysId[f.psysCount] = sid;
						f.psysCount++;
						IceLog("boom tier=%d row=%d col=%d spawn%d psys=0x%X id=0x%X fx=%.0f fy=%.0f img=0x%X",
							tier, row, col, s, psys, sid, fx, fy, (DWORD)g_iceFieldImage);
					}
				}
				IceLog("field created: fields=%d durMs=%u(accum) img=0x%X", g_iceFieldCount, (DWORD)g_iceFieldCs * 10, (DWORD)g_iceFieldImage);
			}

			// ② 冻结时长再断言窗口（仅 2/3 阶：0/1 阶保持原版节奏，避免全屏 Froze 刷副作用）
			if (tier >= 2 && g_iceGraceCount < 16)
			{
				g_iceGrace[g_iceGraceCount].tier = tier;
				g_iceGrace[g_iceGraceCount].remainPoll = ICE_GRACE_POLLS;
				g_iceGraceCount++;
			}
		}
		g_iceBoomReqCount = 0;
	}

	// ---- ② 冻结时长再断言：覆盖原版晚到的 400cs 冻结，确保 2/3阶 8 秒生效 ----
	if (g_iceGraceCount > 0)
	{
		for (int gr = 0; gr < g_iceGraceCount; )
		{
			int freezeCs = (g_iceGrace[gr].tier >= 2) ? g_iceFreezeCs : ICE_FREEZE_DEFAULT_CS;
			for (auto& z : zombies)
				if (z.isValid() && !z.NotExist)
					z.Froze(freezeCs);
			g_iceGrace[gr].remainPoll--;
			if (g_iceGrace[gr].remainPoll <= 0)
			{
				g_iceGrace[gr] = g_iceGrace[g_iceGraceCount - 1]; // 尾删
				g_iceGraceCount--;
			}
			else gr++;
		}
	}

	// ---- ③④ 维护冰法阵：暂停感知到期 + 标记内部僵尸（脆弱 + 减速）----
	// 视觉效果为路灯花光晕贴图换淡蓝高不透明版，生成时一次性 spawn，灯光持续发光无需周期重刷。
	// ★暂停/切后台的倒计时处理：不依赖暂停标志（偏移不可靠，短路曾导致永不 Die → 特效残留）。
	//   靠"单帧跳变 >250ms 不累计"过滤：暂停或切后台期间恢复后单帧 del 巨大 >250ms → 不补算成
	//   运行时间 → 法阵按真实连续运行时间计时，暂停不计时、切后台也不瞬间追平。卡顿 1~2 帧的正常
	//   渐变(16~33ms)照常累计，法阵 20 秒寿命几乎无感延长，绝不残留。
	g_iceVulnZombies.clear();
	if (g_iceFieldCount == 0) return;

	for (int fi = 0; fi < g_iceFieldCount; )
	{
		IceFieldRec& f = g_iceFields[fi];
		// 运行时长累加。del 上限 250ms：暂停/切后台/卡顿的巨大跳帧不补算成时间
		//（否则切后台回来法阵会瞬间到期）；真实连续运行时间照常累计。
		DWORD del = now - f.lastReal;
		f.lastReal = now;
		if (del < 250)
			f.accumMs += del;
		if (f.accumMs >= (DWORD)g_iceFieldCs * 10)
		{
			// 法阵到期：手动 Die 掉持有句柄，保证路灯光光圈随之消失不残留。
			// ★槽位复用防护：Die 前读槽位 Id(+0x28，0x518B90 反汇编实锤) 与创建时比对——
			//   一致=还是我们那个光圈（安全 Die）；不一致/读不了=槽已被游戏回收
			//   复用给了别的特效（此时 Die 会把别人的结构当粒子拆 → 堆损坏），必须跳过。
			//   ★旧版读 +0x9C 是动画池偏移（0x2C 系统槽的越界垃圾），校验随机翻车 →
			//   翻车时只清簿记不杀系统 = 光圈永生（即当年挂起的"领域光圈不消失"bug）
			for (int s = 0; s < f.psysCount && s < 2; s++)
			{
				DWORD psys = f.psys[s];
				DWORD curId = 0;
				bool readable = CrashIsReadable(psys, 0x30);
				if (readable)
					curId = MemSafeRead<DWORD>(psys + 0x28);
				if (readable && curId == f.psysId[s] && curId != 0)
				{
					IceParticleDie(psys);
					IceLog("field expire: Die psys=0x%X id=0x%X OK", psys, curId);
				}
				else
				{
					IceLog("field expire: SKIP psys=0x%X wantId=0x%X curId=0x%X readable=%d (slot recycled)",
						psys, f.psysId[s], curId, readable ? 1 : 0);
				}
			}
			g_iceFields[fi] = g_iceFields[g_iceFieldCount - 1];
			g_iceFieldCount--;
			continue;
		}
		// 3×3 判定（2026-09-13 修正，同毁灭领域）：行用 Row 字段精确判定 |dr|≤1，
		// 列保留 X ±80px。旧实现 Y 用 ±85px 像素窗口，僵尸 Y 相对法阵中心有 ~+15 系统
		// 偏移 → 下行僵尸卡线有效、上行超出无效（用户实测"某一整行不减速/不加脆弱"）。
		for (auto& z : zombies)
		{
			if (!z.isValid() || z.NotExist) continue;
			int dr = z.Row - f.row;
			if (dr < -1 || dr > 1) continue;
			float dx = z.X - f.cx;
			if (dx >= -80.0f && dx <= 80.0f)
			{
				z.Decelerate(100);   // 刷新 1 秒减速，在场期间持续减速
				g_iceVulnZombies.insert(z.GetBaseAddress());
			}
		}
		fi++;
	}
}

static void IceFieldFrame(DWORD boardAddr)
{
	__try
	{
		IceFieldFrameInner(boardAddr);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_iceFxErr++;
	}
}

// ==================== 毁灭菇等阶：轮询帧执行（化灰爆炸 + 毁灭领域）====================
// ① 消费 onPlantRemove 登记的爆炸请求：
//    - 1阶：以毁灭菇格心为圆心 350px 半径内僵尸 z.Blast() 化灰（原版灰烬路径）。
//    - 2阶+：全屏僵尸 Blast() 化灰。
//    - 0阶：不处理（原版爆炸自行覆盖）。
//    ★ 原版毁灭菇爆炸照常发生：半径重叠的僵尸会被化灰两次，
//      ApplyBurn 的 State==2（死亡中）守卫保证重复调用无害。
// ② 3阶+：原地生成 3×3 毁灭领域（视觉暂用寒冰菇冰法阵特效 + 淡蓝贴图），
//    持续 g_iceFieldCs（与 ICESHROOM_FIELD_DURATION 共用参数）。
//    每帧把领域内（±80/±85px，同冰法阵判定）僵尸标记进 g_doomDomainZombies，
//    集合每帧重建 → 僵尸离开/领域到期时穿甲效果自动消失。
//    伤害穿甲结算在 TakeDamage hook（CapBlastDoorDamageWithVuln）内完成：
//    领域内非防爆门僵尸 → 改走 TakeBodyDamage 直接结算本体。
// 计时/槽位复用防护与冰法阵完全一致（暂停感知 250ms 过滤 + Die 前 Id 校验）。
// 领域内随机点撒一撮粒子（轮询帧安全：rand/SeaBurstSpawnParticle 均有轮询帧先例）
static void DoomFieldSprinkle(const DoomFieldRec& f, int effectId)
{
	if (effectId <= 0) return;
	float fx = f.cx + (float)(rand() % 181) - DOOM_SPRINKLE_X;   // X ±90
	float fy = f.cy + (float)(rand() % 191) - DOOM_SPRINKLE_Y;   // Y ±95
	SeaBurstSpawnParticle(fx, fy, effectId);
}

// ★2026-09-12 毒雾改原生粒子定义（覆写 Credits_fog=0x68）：淡入淡出/染色/上升全部在
//   .compiled 内用原生轨道表达，运行时零维护（无需贴图加载/池守卫/逐帧换图）。


static void DoomFieldFrameInner(DWORD boardAddr)
{
	if (!CrashIsReadable(boardAddr, 0x100)) return;
	DWORD now = GetTickCount();

	// ---- ① 消费爆炸请求：化灰 + 领域生成 ----
	if (g_doomBoomReqCount > 0)
	{
		PVZ::Board board(boardAddr);
		auto zombies = board.GetAllZombies();
		for (int q = 0; q < g_doomBoomReqCount; q++)
		{
			int tier = g_doomBoomReqs[q].tier;
			int row  = g_doomBoomReqs[q].row;
			int col  = g_doomBoomReqs[q].col;
			if (tier < 1) continue;

			int centerX = board.GridToXPixel(row, col);
			int centerY = board.GridToYPixel(row, col);
			long long radiusSq = (long long)DOOM_T1_RADIUS * DOOM_T1_RADIUS;
			bool fullScreen = (tier >= 2);

			int blasted = 0;
			for (auto& z : zombies)
			{
				if (!z.isValid() || z.NotExist) continue;
				if (!fullScreen)
				{
					long long dx = (long long)((int)z.X - centerX);
					long long dy = (long long)((int)z.Y - centerY);
					if (dx * dx + dy * dy > radiusSq) continue;
				}
				// 化灰 = 原版灰烬路径 ApplyBurn（内部 State==2 守卫，重复调用无害）
				z.Blast();
				blasted++;
			}
			IceLog("doom boom: tier=%d row=%d col=%d blasted=%d", tier, row, col, blasted);

			// ② 3阶+：原地生成毁灭领域（★底盘已按需求移除，纯雾团表达领域范围）
			//    氛围 = 周期撒余烬(0x4C)+尘烟(0x62)+毒雾(0x68)，特效 ID 可在 ini 换（DOOM_FIELD_*_EFFECT）
			if (tier >= 3 && g_doomFieldCount < 8)
			{
				DoomFieldRec& f = g_doomFields[g_doomFieldCount];
				f.cx = (float)centerX;
				f.cy = (float)centerY;
				f.row = row;       // 3×3 行判定基准（Row 字段，不受像素窗口偏差影响）
				f.accumMs = 0;
				f.lastReal = now;
				f.emberAccum = 0;
				f.dustAccum = 0;
				f.fogAccum = 0;
				f.fogImgCur = 0;   // 0=未换过档 → 首个轮询帧执行一次换图
				f.psysCount = 0;
				f.gen = ++g_doomFieldGen;
				g_doomFieldCount++;
				// 开场爆发：立即撒 3 撮余烬 + 3 撮尘烟（领域刚出现就有"余爆未熄"感）
				for (int b = 0; b < 3; b++)
				{
					DoomFieldSprinkle(f, g_doomEmberEffect);
					DoomFieldSprinkle(f, g_doomDustEffect);
				}
				// 紫雾覆盖层：0x68 Credits_fog 槽（已覆写为 LanternShine 静态变体：无旋转/单粒子/
				// alpha 恒定/scale 1:1，见 doomfog_area_static.particles.xml）+ OverrideImage 换紫黑
				// 雾贴图。原 0x2E 灯光特效废弃——其 ParticleSpinSpeed ±20~40°/s 会把矩形贴图转歪，
				// 且 SpawnMinActive=10 叠 10 张各自旋转的图（v1 大紫饼元凶之一）。到期校验 Id 后 Die。
				if (g_doomFogEnabled)
				{
					// ★ 2026-10-16：限流（原本"缺图时每次创建领域都重试"，每次漏 ~4KB 堆）
					if (ImageLoadRetryAllowed(10))
						LoadDoomFogAreaImages();   // 内部幂等（两张齐才跳过）
					if (g_doomFogImgA80)
					{
						// 渲染层（2026-09-12 用户需求：雾在植物与僵尸之下）：取全场植物/僵尸的
						// 最小 Layer（GameObject::Layer@+0x20"绘制图层编号"）再降一个 row 单位
						// 0x2710，保证严格绘制在其下层；无样本时兜底 0x40000（低于 0x61A80 通用层）。
						DWORD fogLayer = 0x40000;
						DWORD minL = 0;
						auto plantsL = board.GetAllPlants();
						for (auto& p : plantsL)
						{
							if (!p.isValid() || p.NotExist) continue;
							DWORD L = (DWORD)p.Layer;
							if (L > 0x2710 && (minL == 0 || L < minL)) minL = L;
						}
						for (auto& z : zombies)
						{
							if (!z.isValid() || z.NotExist) continue;
							DWORD L = (DWORD)z.Layer;
							if (L > 0x2710 && (minL == 0 || L < minL)) minL = L;
						}
						if (minL != 0) fogLayer = minL - 0x2710;
						IceLog("doom fog layer: minL=0x%X fogLayer=0x%X", minL, fogLayer);
						DWORD psys = SeaBurstSpawnParticleEx(f.cx, f.cy, 0x68, fogLayer);
						if (psys && psys >= 0x10000)
						{
							SeaBurstOverrideImage(psys, g_doomFogImgA22);   // 淡入起步
							DWORD sid = 0;
							if (CrashIsReadable(psys, 0x30))
								sid = MemSafeRead<DWORD>(psys + 0x28);
							f.psys[0] = psys;
							f.psysId[0] = sid;
							f.psysCount = 1;
						}
					}
				}
				IceLog("doom field created: fields=%d durCs=%d ember=%d dust=%d fogImg=0x%X",
					g_doomFieldCount, g_iceFieldCs, g_doomEmberEffect, g_doomDustEffect, g_doomFogImgA80);
			}
		}
		g_doomBoomReqCount = 0;
	}

	// ---- ② 维护毁灭领域：到期移除 + 每帧重建领域内僵尸集合 ----
	g_doomDomainZombies.clear();
	if (g_doomFieldCount == 0)
	{
		g_doomBurnReqCount = 0;   // 无领域：丢弃滞留请求（防跨关残留）
		return;   // 领域已全部到期：不再生成任何粒子；已撒出的雾/烬自带寿命自然消亡
	}

	PVZ::Board board2(boardAddr);
	auto zombies2 = board2.GetAllZombies();
	for (int fi = 0; fi < g_doomFieldCount; )
	{
		DoomFieldRec& f = g_doomFields[fi];
		DWORD del = now - f.lastReal;
		f.lastReal = now;
		if (del < 250)
		{
			f.accumMs += del;
			f.emberAccum += del;
			f.dustAccum += del;
			f.fogAccum += del;
		}
		if (f.accumMs >= (DWORD)g_iceFieldCs * 10)
		{
			// 到期：Die 雾覆盖层（槽位 Id 校验防复用拆坏堆，冰法阵同款防护）；
			// 余烬/尘烟粒子自带寿命自然消亡
			for (int s = 0; s < f.psysCount && s < 2; s++)
			{
				DWORD dpsys = f.psys[s];
				bool readable = CrashIsReadable(dpsys, 0x30);
				DWORD curId = readable ? MemSafeRead<DWORD>(dpsys + 0x28) : 0;
				if (readable && curId == f.psysId[s] && curId != 0)
				{
					IceParticleDie(dpsys);
					IceLog("doom field expire: Die fog psys=0x%X id=0x%X OK", dpsys, curId);
				}
				else
				{
					IceLog("doom field expire: SKIP fog psys=0x%X wantId=0x%X curId=0x%X readable=%d",
						dpsys, f.psysId[s], curId, readable ? 1 : 0);
				}
			}
			g_doomFields[fi] = g_doomFields[g_doomFieldCount - 1];
			g_doomFieldCount--;
			continue;
		}
		// 雾层淡入/淡出：age<600ms 或剩<600ms 用 a22 淡档，中间用 a80 常驻档
		//（换图前校验槽位 Id 防复用写坏堆，冰法阵同款防护）
		if (f.psysCount > 0 && g_doomFogEnabled && g_doomFogImgA22 && g_doomFogImgA80)
		{
			int total = g_iceFieldCs * 10;
			DWORD want = (f.accumMs < (DWORD)DOOM_FOG_FADE_MS
				|| f.accumMs + (DWORD)DOOM_FOG_FADE_MS >= (DWORD)total)
				? g_doomFogImgA22 : g_doomFogImgA80;
			if (want != f.fogImgCur)
			{
				f.fogImgCur = want;
				DWORD fpsys = f.psys[0];
				bool readable = CrashIsReadable(fpsys, 0x30);
				DWORD curId = readable ? MemSafeRead<DWORD>(fpsys + 0x28) : 0;
				if (readable && curId == f.psysId[0] && curId != 0)
					SeaBurstOverrideImage(fpsys, want);
			}
		}
		// 周期撒播：余烬（火球落地爆开）+ 尘烟（走路扬尘），随机点分布在 3×3 判定区
		// 撒播粒子自带寿命、自然消亡，无需登记清理（与底盘光圈不同）
		if (f.emberAccum >= DOOM_EMBER_INTERVAL_MS)
		{
			f.emberAccum = 0;
			DoomFieldSprinkle(f, g_doomEmberEffect);
		}
		if (f.dustAccum >= DOOM_DUST_INTERVAL_MS)
		{
			f.dustAccum = 0;
			DoomFieldSprinkle(f, g_doomDustEffect);
		}
		// 3×3 判定（2026-09-13 修正）：行用 Row 字段精确判定（|dr|≤1），列保留 X ±80px。
		// ★旧实现 Y 用 ±85px 像素窗口：僵尸 Y 相对领域中心有约 +15 系统偏移 → 下行僵尸
		//   dy≈+85 卡进边界（有效）、上行 dy≈−115 超出（无效）→ 用户实测"上面一行有雾贴图
		//   但无穿甲/紫焰"。Row 判定无此偏差（该窗口问题自冰法阵沿用，非新引入）。
		for (auto& z : zombies2)
		{
			if (!z.isValid() || z.NotExist) continue;
			int dr = z.Row - f.row;
			if (dr < -1 || dr > 1) continue;
			float dx = z.X - f.cx;
			if (dx >= -80.0f && dx <= 80.0f)
				g_doomDomainZombies.insert(z.GetBaseAddress());
		}
		fi++;
	}

	// 领域内受伤紫焰：消费 hook 登记的 POD 请求（重活集中在此，事件帧只登记）
	if (g_doomBurnReqCount > 0)
	{
		int bn = g_doomBurnReqCount;
		if (bn > DOOM_BURN_REQ_MAX) bn = DOOM_BURN_REQ_MAX;
		// ★ LawnApp 全局指针（0x6A9EC0）。注意不能读 [Board+0]——Board 继承 Widget 而非
		//   GameObject，+0 不是 LawnApp（曾因此让 0x453C30 拿垃圾 eax 返回 0：called=1 created=0）
		DWORD lawnApp = MemSafeRead<DWORD>(0x6A9EC0);
		for (int i = 0; i < bn; i++)
			DoomPurpleBurnFx(lawnApp, g_doomBurnReqX[i], g_doomBurnReqY[i], g_doomBurnReqLayer[i]);
		g_doomBurnReqCount = 0;
		// 位置诊断（限流 5s，取本批第 1 条）：僵尸坐标候选字段 + 领域中心 + 实际传参
		// 用途：用户回报偏移时用真实数值定坐标公式（各字段语义靠数值反推，不猜）
		static DWORD s_burnPosTick = 0;
		DWORD tk3 = GetTickCount();
		if (tk3 - s_burnPosTick > 5000)
		{
			s_burnPosTick = tk3;
			float fcx = (g_doomFieldCount > 0) ? g_doomFields[0].cx : -1.0f;
			float fcy = (g_doomFieldCount > 0) ? g_doomFields[0].cy : -1.0f;
			IceLog("doom burn pos: z2C=%.1f z30=%.1f z34=%.1f row=%d | field=(%.1f,%.1f) | passX=%.1f passY=%.1f",
				g_doomBurnReqX[0], g_doomBurnReqY[0], g_doomBurnReqZ34[0], g_doomBurnReqRow[0],
				fcx, fcy, g_doomBurnReqX[0], g_doomBurnReqY[0]);
		}
		// 诊断（限流 5s）：called=0 → 登记没进来；created<called → 0x453C30 创建失败
		static DWORD s_burnLogTick = 0;
		DWORD tk2 = GetTickCount();
		if (tk2 - s_burnLogTick > 5000)
		{
			s_burnLogTick = tk2;
			IceLog("doom burn: called=%d created=%d", g_doomBurnFxCalled, g_doomBurnFxCreated);
		}
	}
}

static void DoomFieldFrame(DWORD boardAddr)
{
	__try
	{
		DoomFieldFrameInner(boardAddr);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_doomFxErr++;
	}
}

extern "C" __declspec(dllexport) void onGameObjectsUpdate(DWORD boardAddress)
{
	// ★ 帧首堆完整性哨兵（在 CRASH_STEP 之前调用，记录的是上一帧结束时的 step）
	HeapWatchTick();
	CRASH_STEP("onGameObjectsUpdate:enter");
	__try
	{
		onGameObjectsUpdateInner(boardAddress);
	}
	__except (CrashSwallowFilter(GetExceptionInformation()))
	{
	}
}

// 每帧轮询的真正实现（无 __try —— 内含大量 std::vector/map 局部对象，
// 与 __try 同函数会触发 MSVC C2712；与 UpdatePoisonFrame/Inner 同模式）
static void onGameObjectsUpdateInner(DWORD boardAddress)
{
	// Board 指针有效性校验：退出关卡/切场景/暂停恢复的第一帧可能拿到 0 或已释放地址，
	// 后面大量 [boardAddress+xxx] 读写会直接踩空 → 提前返回，等下一帧拿到合法 Board。
	if (!CrashIsReadable(boardAddress, 0x100))
		return;

	// ===== 植物经验存档：还原尝试 + 周期落盘 =====
	if (g_expSaveRestorePending)
	{
		// 关卡刚初始化（onBoardInitAfter 挂起）：立即开始逐帧尝试还原。
		// ★不等 onNewGame：恢复关卡(resume)时该事件不触发，等它会把还原卡死。
		// 若 onNewGame 之后才触发（清空经验表），RearmAfterNewGame 会从内存快照重新还原。
		g_expSaveRestoreDeadline--;
		PlantExpTryRestore(boardAddress);
		if (g_expSaveRestorePending && g_expSaveRestoreDeadline <= 0)
			PlantExpSaveFinishRestore(true, "discard: restore window expired");
	}
	else
	{
		// 周期落盘 + 布局变化补写（轮询帧，崩溃铁律允许 fopen）
		g_expSaveAutosaveCounter++;
		if ((g_expSaveDirty && g_expSaveAutosaveCounter >= EXP_SAVE_DIRTY_INTERVAL)
			|| g_expSaveAutosaveCounter >= EXP_SAVE_INTERVAL)
		{
			PlantExpSaveWriteFile(boardAddress);
			g_expSaveAutosaveCounter = 0;
			g_expSaveDirty = false;
		}
	}

	// ===== 经验文字已改为自绘字形 =====
	// 旧的"强制钱币计数器常驻"补丁（InstallForceCoinBank）已停用：
	// 它只是让钱币绘制顺带把 DDraw/DC 状态刷成可用，属于绕路 hack，
	// 会在左下角强制显示钱币数，且仍无法解决字号随横幅变化的问题。
	// 现在经验文字走 NativeDrawExpGlyphs（游戏自带字形图 + DrawImage），
	// 与 surface DC / 字体对象 / 钱币绘制顺序完全无关。

	// ===== 三叶草延迟触发（先分配挂起的死亡经验，保证三叶草读到正确等阶）=====
	// 铲同行植物 → onPlantRemove 挂起经验 → 这里分配（可能分给三叶草）→ 再读经验判等阶
	// 吹飞在 Update 阶段(0x460F4B)早于绘制阶段的经验分配，故延迟一帧到此处触发
	if (!g_pendingBloverTriggers.empty())
	{
		if (g_lastDeathRow >= 0)
		{
			DistributeRowExperience(g_lastDeathRow, 0, g_lastDeathExp);
			g_lastDeathRow = -1;
			g_lastDeathExp = 0;
		}
		for (int addr : g_pendingBloverTriggers)
			TriggerBloverEffects((DWORD)addr);
		g_pendingBloverTriggers.clear();
	}

	// ===== hook 站点看门狗（修改器共存）：每 2 秒巡检，被夺走时留痕 HOOKCLOBBER =====
	HookSiteWatchdog();

	// ===== 杨桃齐射尾 hook 延迟安装（游戏代码解密完成后，防止启动早期读到垃圾原代码）=====
	if (!g_starVolleyHookInstalled)
	{
		g_starVolleyHookInstalled = true;
		InstallStarVolleyHook();
	}

	// ===== 魅惑菇被吃 hook 延迟安装（0x52xxxx 区域运行时解密后才可核对字节）=====
	if (!g_hypnoHookInstalled)
	{
		g_hypnoHookInstalled = true;
		InstallHypnoShroomHook();
	}

	// ===== 魅惑菇1阶：延迟回满血（hook 在魅惑流程前触发，下一帧写入防止被覆盖）=====
	if (!g_hypnoPendingHeals.empty())
	{
		for (auto& kv : g_hypnoPendingHeals)
		{
			PVZ::Zombie z(kv.first);
			if (!z.isValid() || z.NotExist)
				continue;
			z.BodyHealth = z.BodyMaxHealth;
			z.HelmHealth = z.HelmMaxHealth;
			z.ShieldHealth = z.ShieldMaxHealth;
		}
		g_hypnoPendingHeals.clear();
	}
	// 防御：齐射上限复位（齐射内 star0 置位/star末 复位均同步完成，此处兜底异常残留；
	// 齐射发生在本回调之后的对象更新阶段，同 tick 内的暴击不受影响）
	g_starVolleyLimit = 5;

	// ===== 寒冰射手自定义贴图延迟加载（首次进入关卡时执行，此时游戏资源已就绪）=====
	if (!g_icicleImageLoaded && ImageLoadRetryAllowed(7))
	{
		g_icicleImageLoaded = true;
		// 冰锥（5阶）
		Draw::PString filename = Draw::ToString("images\\ProjectileIcicle.png");
		Draw::PString variant = Draw::ToString("");
		DWORD isNew = 0;
		DWORD sharedImg = Draw::GetSharedImage(isNew, variant, filename);
		if (sharedImg != 0)
			g_icicleImageAddr = Draw::SharedImageRefToImage(sharedImg);
		// 雪晶（3/4阶冻结子弹）
		Draw::PString filename2 = Draw::ToString("images\\ProjectileSnowCrystal.png");
		DWORD sharedImg2 = Draw::GetSharedImage(isNew, variant, filename2);
		if (sharedImg2 != 0)
			g_snowCrystalImageAddr = Draw::SharedImageRefToImage(sharedImg2);
		// 西瓜大炮弹放大贴图（5阶西瓜投手最后一发，1.5x Melonpult_melon）
		Draw::PString filename3 = Draw::ToString("images\\ProjectileMelonBig.png");
		DWORD sharedImg3 = Draw::GetSharedImage(isNew, variant, filename3);
		if (sharedImg3 != 0)
			g_melonBigImageAddr = Draw::SharedImageRefToImage(sharedImg3);
		// 小冰瓜 80% 贴图（5阶冰西瓜大招散射弹，0.8x WinterMelon_projectile）
		Draw::PString filename4 = Draw::ToString("images\\ProjectileIceMelonSmall.png");
		DWORD sharedImg4 = Draw::GetSharedImage(isNew, variant, filename4);
		if (sharedImg4 != 0)
			g_iceMelonSmallImageAddr = Draw::SharedImageRefToImage(sharedImg4);
		// 击退弹贴图（豌豆射手3阶+，标记97）
		Draw::PString filename5 = Draw::ToString("images\\ProjectileKnockbackPea.png");
		DWORD sharedImg5 = Draw::GetSharedImage(isNew, variant, filename5);
		if (sharedImg5 != 0)
			g_knockbackPeaImageAddr = Draw::SharedImageRefToImage(sharedImg5);
	}

	// ===== 冰锥贴图 hook 延迟安装（游戏代码解密完成后，防止启动早期读到垃圾原代码）=====
	if (!g_icicleHookInstalled)
	{
		g_icicleHookInstalled = true;
		InstallIcicleImageHook();
	}

	// ===== 花盆种植放宽 hook 延迟安装（进入关卡后安装，此时游戏代码已就绪）=====
	if (!g_flowerPotHookInstalled)
	{
		g_flowerPotHookInstalled = true;
		InstallFlowerPotHook();
	}

	// ===== 花盆装水贴图（水生植物种在花盆上 → Pot_top → Pot_top2）=====
	// 贴图延迟加载（与冰锥/金盏花同模式：onGameObjectsUpdate 首次执行时资源已就绪）
	if (!g_potTopImageLoaded && ImageLoadRetryAllowed(0))
	{
		g_potTopImageLoaded = true;
		LoadPotTopImages();
	}
	{
		PVZ::Board board(boardAddress);
		if (board.GetBaseAddress() && (g_potTop2Image != 0 || g_potTopOrigImage != 0))
		{
			auto plants = board.GetAllPlants();
			// 第一遍：收集所有水生植物所在格子（cellKey = row*10 + col）
			std::set<int> waterCells;
			for (auto& plant : plants)
			{
				if (!plant.isValid() || plant.NotExist) continue;
				if (IsAquaticPlantType((int)plant.Type))
					waterCells.insert((int)plant.Row * 10 + (int)plant.Column);
			}
			// 第二遍：花盆按格子上是否有水生植物切换贴图
			for (auto& plant : plants)
			{
				if (!plant.isValid() || plant.NotExist) continue;
				if (plant.Type != SeedType::FlowerPot) continue;
				int cellKey = (int)plant.Row * 10 + (int)plant.Column;
				ApplyPotTopTexture(plant.GetBaseAddress(), waterCells.find(cellKey) != waterCells.end());
			}
		}
	}

	// ===== 获得关卡 hook 延迟安装（GetAwardSeedForLevel @ 0x453A90，游戏代码就绪后）=====
	if (!g_awardSeedHookInstalled)
	{
		g_awardSeedHookInstalled = true;
		InstallAwardSeedHook();
	}

	// ===== 选卡解锁判定 hook 延迟安装（IsSeedTypeUnlocked 尾部 @ 0x453C17）=====
	if (!g_unlockHookInstalled)
	{
		g_unlockHookInstalled = true;
		InstallUnlockHook();
	}

	// ===== 三叶草"开始吹"时刻 hook 延迟安装（游戏代码解密完成后）=====
	if (!g_bloverHookInstalled)
	{
		g_bloverHookInstalled = true;
		InstallBloverHook();
	}

	// ===== 卷心菜投手散射 hook 延迟安装（游戏代码解密完成后）=====
	if (!g_cabbageHookInstalled)
	{
		g_cabbageHookInstalled = true;
		InstallCabbageHooks();
	}

	// ===== 火炬树桩 过火 hook 延迟安装（游戏代码解密完成后）=====
	if (!g_torchwoodHookInstalled)
	{
		g_torchwoodHookInstalled = true;
		InstallTorchwoodHooks();
	}

	// ===== 豌豆染色 hook 延迟安装（游戏代码解密完成后，同冰锥贴图 hook）=====
	if (!g_peaColorHookInstalled)
	{
		g_peaColorHookInstalled = true;
		InstallPeaColorHook();
	}

	// ===== 裂荚射手 双向射击 hook 延迟安装（游戏代码解密完成后）=====
	if (!g_splitPeaHookInstalled)
	{
		g_splitPeaHookInstalled = true;
		InstallSplitPeaHooks();
	}

	// ===== 玉米投手 黄油判定 hook 延迟安装（游戏代码解密完成后）=====
	if (!g_cornButterHookInstalled)
	{
		g_cornButterHookInstalled = true;
		InstallKernelpultButterHook();
	}

	// ===== 玉米投手：攻击计数落账 + 状态/距离缓存清理 =====
	CRASH_STEP("corn:hit-accounting");
	// ★ 事件帧只登记 POD pending，这里（轮询帧）才写 map，防事件帧 map 插入崩溃
	if (g_cornPendingCount > 0)
	{
		for (int i = 0; i < g_cornPendingCount; i++)
		{
			if (g_cornPending[i].plant && g_cornPending[i].zombie)
			{
				auto& zm = g_cornPultHits[g_cornPending[i].plant];
				if (zm[g_cornPending[i].zombie] < 1000)
					zm[g_cornPending[i].zombie]++;
			}
		}
		g_cornPendingCount = 0;
	}
	// 僵尸已移除/植物已铲除的记录及时清理（防内存池地址复用误判）
	for (auto it = g_cornPultHits.begin(); it != g_cornPultHits.end(); )
	{
		DWORD pAddr = it->first;
		bool pAlive = false;
		if (pAddr != 0)
		{
			int ptype = MemSafeRead<int>(pAddr + 0x24);
			int pnot = MemSafeRead<BYTE>(pAddr + 0x141);
			pAlive = (ptype == (int)SeedType::Kernelpult) && (pnot == 0);
		}
		if (!pAlive) { it = g_cornPultHits.erase(it); continue; }

		auto& zm = it->second;
		for (auto zit = zm.begin(); zit != zm.end(); )
		{
			bool zAlive = (zit->first != 0)
				&& (MemSafeRead<BYTE>(zit->first + 0xEC) == 0);
			if (!zAlive) zit = zm.erase(zit);
			else zit++;
		}
		it++;
	}
	// 玉米投手缓存：清理已移除植物的缓存 + 刷新存活玉米投手(1阶+)的本行最靠前僵尸
	// ★ 在轮询帧做完整扫描（GetAllZombies 属重操作），事件帧只读 g_cornFrontZombie/Dist
	for (auto it = g_cornFrontDist.begin(); it != g_cornFrontDist.end(); )
	{
		DWORD pAddr = it->first;
		bool alive = ((int)pAddr >= 0x10000)   // 跳过 0/-1 等哨兵键（崩溃残留防护）
			&& (g_plantExperience.find(pAddr) != g_plantExperience.end());
		if (!alive) it = g_cornFrontDist.erase(it);
		else it++;
	}
	for (auto it = g_cornFrontZombie.begin(); it != g_cornFrontZombie.end(); )
	{
		DWORD pAddr = it->first;
		bool alive = (pAddr != 0)
			&& (g_plantExperience.find(pAddr) != g_plantExperience.end());
		if (!alive) it = g_cornFrontZombie.erase(it);
		else it++;
	}
	for (auto& kv : g_plantExperience)
	{
		DWORD pAddr = kv.first;
		if (!pAddr) continue;
		if (MemSafeRead<int>(pAddr + 0x24) != (int)SeedType::Kernelpult) continue;
		int cpTier = GetPlantTier((int)SeedType::Kernelpult, kv.second);
		if (cpTier < 1) continue;   // 1阶起才需要（1阶黄油/2阶距离）
		// 本行最靠前（X 最小）存活僵尸（索敌目标）
		DWORD frontZombie = 0;
		float frontX = -1.0f;
		DWORD boardAddr = MemSafeRead<int>(pAddr + 4);
		if (boardAddr == boardAddress)   // 仅当前板（防陈旧板指针/场景切换）
		{
			int row = MemSafeRead<int>(pAddr + 0x1C);
			PVZ::Board brd(boardAddr);
			auto zombies = brd.GetAllZombies();
			for (auto& z : zombies)
			{
				if (z.NotExist) continue;
				if ((int)z.Row != row) continue;
				if (z.Hypnotized) continue;   // 魅惑僵尸不索敌
				float zx = z.X;
				if (frontX < 0.0f || zx < frontX)
				{
					frontX = zx;
					frontZombie = z.GetBaseAddress();
				}
			}
		}
		float dist = -1.0f;
		if (frontX >= 0.0f)
		{
			int plantCol = MemSafeRead<int>(pAddr + 0x28);
			dist = ((float)(plantCol * 80 + 40) - frontX) / 80.0f;
		}
		g_cornFrontZombie[pAddr] = frontZombie;
		g_cornFrontDist[pAddr] = dist;
	}

	// ===== 三线射手：v2 零 hook 方案，无 hook 安装（等阶逻辑在 onGameObjectsUpdate）=====

	// ===== 撑杆司令：每帧轮询（标记司令 + 移速 + 二段跳）=====
	CRASH_STEP("polecommander");
	// ★★★ 重大重构：弃用框架事件（ZombieInitAfterEvent@0x524035 / FullJumpEvent@0x52601B）！
	//   实测日志（D:\pvz_pole_debug.txt [probe]）证实：
	//   0x524035 是函数尾部（原始 5F 5E 5B 8B E5 5D C2 14 = pop×3+mov esp,ebp+pop ebp+ret 0x14），
	//   0x52601B 是指令中间（D9 46 2C C6 44 ... 截断 mov byte 指令）——事件 hook 会截断指令，
	//   僵尸创建流程执行到 hook 点 ret 0x14 弹飞栈 → 进关瞬间崩溃，且回调从未触发（0 条 [mark]）。
	//   改为纯内存轮询：零 hook、零指令截断、零崩溃风险。
	// ===== 撑杆司令：波次变化检测（重置类型3槽位计数，须在轮询标记之前）=====
	CRASH_STEP("polecommander:wave");
	UpdatePoleVaulterWaveTracking(boardAddress);
	UpdatePoleCommanderFrame(boardAddress);

	// ===== 保护伞：每帧轮询（咖啡豆唤醒检测 + T1豌豆反弹/T2弹飞小鬼/T3弹飞起跳僵尸）=====
	CRASH_STEP("umbrella");
	UpdateUmbrellaFrame(boardAddress);

	// ===== 金盏花：每帧轮询（唤醒检测 + 形态染色 + 右键切换 + 杀虫剂tick + 留声机到期）=====
	CRASH_STEP("marigold");
	// 产出 hook（0x45FB1B→0x45FB1D call 0x40CB10）延迟安装；产出物图片延迟加载
	if (!g_mgHookInstalled)
	{
		g_mgHookInstalled = true;
		InstallMarigoldProduceHook();
	}
	if (!g_mgImagesLoaded && ImageLoadRetryAllowed(1))
	{
		g_mgImagesLoaded = true;
		LoadMarigoldImages();
	}
	UpdateMarigoldFrame(boardAddress);
	// ★ 冰西瓜大招散射放在本帧最前段执行（紧邻读取，无中间重活）：即便本帧后续机制异常，
	//   VOLLEY 日志也已落盘，便于定位"散射从第 1 只开始"是否为发射侧问题。
	IceMelonVolleyFrame(boardAddress);      // 冰西瓜 5阶：消费"待开大"队列 → 散射小冰瓜
	UpdateMelonChooseFrame(boardAddress);   // 西瓜投手：T3提示轮询 + 选择窗口状态校验
	MelonCannonTick(boardAddress);          // 西瓜大炮：溅射结算（延迟一帧）+ 每帧清索敌标签
	IceMelonFreezeFrame(boardAddress);      // 冰西瓜 4阶：消费"待冻结"队列 → 冻结4秒 + 解冻后10秒减速

	// ===== 防爆门僵尸：每帧轮询（标记防爆门 + 铁桶贴图重设）=====
	CRASH_STEP("blastdoor");
	UpdateBlastproofDoorFrame(boardAddress);

	// ===== 剧毒体系：每帧轮询（UnLock 解锁 reanim 颜色 + 带毒僵尸变绿 + 每秒 tick 伤害 + 兜底清理）=====
	CRASH_STEP("poison");
	UpdatePoisonFrame(boardAddress);

	// ===== 豌豆染色：每帧轮询（Type 6 火球 = reanim 轨道染色，同剧毒机制写 0xA0 池项 +0x48）=====
	if (!g_iceFireImagesLoaded && ImageLoadRetryAllowed(2))
	{
		g_iceFireImagesLoaded = true;
		LoadIceFireImages();
	}
	CRASH_STEP("peatint");
	ApplyPeaTintFrame(boardAddress);

	// ===== 究极大喷菇：每帧轮询（接管大喷菇攻击节奏 → 精确 0.5s 一次；hook 延迟安装）=====
	CRASH_STEP("ultfume");
	UpdateUltFumeFrame(boardAddress);

	// ===== 大喷菇等阶：每帧轮询（攻速钉 [plant+0x5C] + 5阶平滑击退；hook 延迟安装）=====
	// 与 UltFume 互斥（ULF_ENABLED=1 时本模块自动跳过，见 FumeTierFrameInner）
	CRASH_STEP("fumeshroom");
	UpdateFumeTierFrame(boardAddress);

	// ===== 寒冰菇等阶：每帧轮询（冻结 + 命中伤害 + 冰法阵 + 脆弱/减速，消费 onPlantRemove 登记）=====
	CRASH_STEP("iceshroom");
	IceFieldFrame(boardAddress);

	// ===== 毁灭菇等阶：每帧轮询（化灰爆炸 + 毁灭领域，消费 onPlantRemove 登记）=====
	CRASH_STEP("doomshroom");
	DoomFieldFrame(boardAddress);

	// ===== 坚果墙：每帧轮询（升级瞬间回满血）=====
	CRASH_STEP("wallnut");
	WallnutTierFrame(boardAddress);

	// ===== 高坚果：等阶轮询（血量阶梯 + 回满血 + 3阶累计受伤击退）=====
	CRASH_STEP("tallnut");
	TallnutFrame(boardAddress);

	// ===== 大蒜：等阶轮询（1阶血量阶梯 + 2阶方向表维护）=====
	// GARLIC_ENABLED：1=全开（默认）；2=诊断模式（只做帧轮询，不装 hook、不画箭头）；
	//                 0=整段停用（便于二分排障）
	CRASH_STEP("garlic");
	if (g_garlicEnabled)
	{
	GarlicFrame(boardAddress);
	}
	// 诊断模式(2) 不装任何 hook —— 用来判定"崩溃是否由 hook 引起"
	if (g_garlicEnabled == 1)
	{
	// ===== 大蒜：换行方向 patch 延迟安装（0x52B902 随机±1 分支 → GarlicPickRow）=====
	// 0x52xxxx 区域运行时才解密，字节不符则下帧重试；连续失败 120 帧后标记 -1 不再重试
	// （避免每帧重试刷爆日志/耗时）。装后回读校验，只读 .text 会在此暴露。
	if (g_garlicRowHookState == 0)
	{
		if (InstallGarlicRowHook())
		{
			g_garlicRowHookState = 1;
			GarlicDebugReport("rowhook installed");
		}
		else if (++g_garlicRowHookTries > 120)
		{
			g_garlicRowHookState = -1;
			GarlicDebugReport("rowhook FAILED(giveup)");
		}
	}
	// ===== 大蒜：3阶免疫碾压 =====
	// ★ 碾压/砸扁的唯一出口 = Plant::Squish(0x462B80)，其入口 hook 与高坚果共用，
	//   不在此处重复安装（重复安装会互相覆盖）。大蒜 3 阶的免疫判定已并入
	//   TallnutAbsorbKill 首段（见"高坚果等阶机制"段）。该入口已覆盖三条来源：
	//   巨人遍历器 A(0x534BDC) / 巨人遍历器 B(0x53502E) / 车类 0x52E920。
	// ===== 大蒜：3阶"巨人不砸"（两条遍历器 call → GarlicAwareSquish）=====
	// 与高坚果 HookB 不冲突也不依赖顺序：本 hook 只改 0x534BDC/0x53502E 两条 call 的
	// rel32 目标（校验的是"call 目标 == 0x462B80"），完全不碰 0x462B80 入口本身。
	if (g_garlicSmashHookState == 0)
	{
		if (InstallGarlicSmashSkipHook())
		{
			g_garlicSmashHookState = 1;
			GarlicDebugReport("smashhook installed");
		}
		else if (++g_garlicSmashHookTries > 120)
		{
			g_garlicSmashHookState = -1;
			GarlicDebugReport("smashhook FAILED(giveup)");
		}
	}
	}   // end if (g_garlicEnabled == 1)
	// ===== 大蒜：诊断心跳（仅 GARLIC_DEBUG=1 时每 300 帧一行）=====
	if (g_garlicDebug && (g_garlicFrameTick % 300) == 0)
		GarlicDebugReport("hb");

	// ===== 高坚果：抗秒杀 hook 延迟安装（0x52/0x53 区域运行时解密，逐字节核对，
	//       不符则下帧重试；全部安装失败=无抗秒杀但绝不崩溃）=====
	if (!g_tallnutSquishHookInstalled)
	{
		bool a = InstallTallnutSquishHookA();   // 车类碾压（0x52E920）
		bool b = InstallTallnutSquishHookB();   // 锤砸/踩踏压扁（0x462B80）
		g_tallnutSquishHookInstalled = (a && b);
	}
	if (!g_tallnutJalaHookInstalled)
	{
		g_tallnutJalaHookInstalled = InstallTallnutJalaHook();  // 辣椒僵尸烧毁（0x527729）
	}

	// ===== 磁力菇等阶机制：hook 延迟安装 + 每帧轮询 =====
	// 4 个 hook：0x461610 吸到铁器登记 / 0x461E3C 消化完成登记 /
	//            0x4620F4 2阶吸铁半径 +90 / 0x52FCF0 啃食先扣护盾。
	// 经验结算、上护盾、3阶索敌扔铁器、飞行表现全部在 MagFrame 轮询帧完成。
	CRASH_STEP("magnet");
	MagInstallHooks();
	MagFrame(boardAddress);

	// ===== 防爆门僵尸：限伤 hook 延迟安装（游戏代码解密完成后，含运行时序言探测）=====
	// 与撑杆司令同理：0x52/0x53 区域运行时可能解密，安装前逐字节核对运行时字节；
	// 不一致则跳过（不装=无限伤但绝不崩溃），重试 120 帧后放弃防刷屏
	if (!g_blastHooksReady && !g_blastHooksGivenUp)
	{
		if (InstallBlastDamageHooks())
			g_blastHooksReady = true;
		else if (++g_blastHookTries > 120)
			g_blastHooksGivenUp = true;
	}
	// ===== 防爆门僵尸：灰烬化灰拦截 hook（ApplyBurn@0x532B70）延迟安装 =====
	// 灰烬爆炸走 ApplyBurn 直接化灰（不走伤害结算）→ 铁门存在时拦截并改为限伤伤害。
	// 在限伤 hook 阶段落定后独立安装（探测通过才装；即使限伤 hook 全部失败，
	// 拦截路径自带的 200 伤害值依然能限伤）
	if (!g_blastBurnHookInstalled && (g_blastHooksReady || g_blastHooksGivenUp))
	{
		g_blastBurnHookInstalled = InstallBlastBurnHook();
	}
	// ===== 防爆门僵尸：大嘴花撕咬 hook（0x461451）延迟安装 =====
	// 需求：防爆门**不能被一口吞**，要像对巨人一样撕咬掉血（40/口）。
	// 目标是防爆门时强制 dl=1 → 走原版完整巨人撕咬路径（含动画准备）
	if (!g_blastChomperHookInstalled && (g_blastHooksReady || g_blastHooksGivenUp))
	{
		g_blastChomperHookInstalled = InstallBlastChomperHook();
	}
	// ===== 植物数组"已释放对象"防御守卫（0x463920）延迟安装 =====
	// 消灭"巨人群殴中 0x463928 崩溃"（某植物被堆损坏清 0 首字段后仍被遍历）
	if (!g_blastFreedPlantGuardInstalled && (g_blastHooksReady || g_blastHooksGivenUp))
	{
		g_blastFreedPlantGuardInstalled = InstallBlastFreedPlantGuard();
	}
	// ===== 同类守卫 · Plant::Update 尾部（0x463ED2）延迟安装 =====
	// 消灭 0x46441F 崩溃（fault=0x820：植物首字段被清 0 / this 游离后仍进 0x464DB0→0x464410/0x464480）
	if (!g_blastFreedPlantTailGuardInstalled && (g_blastHooksReady || g_blastHooksGivenUp))
	{
		g_blastFreedPlantTailGuardInstalled = InstallBlastFreedPlantTailGuard();
	}
	// ===== 防爆门僵尸：大嘴花索敌兜底 hook（0x46143C）延迟安装 =====
	// FindTargetZombie 对大嘴花可能返回 0（目标丢失→走咬合）→ 索敌失败时扫描防爆门
	// （撕咬的前提是 esi=防爆门，索敌兜底保证目标存在）
	if (!g_blastFindHookInstalled && (g_blastHooksReady || g_blastHooksGivenUp))
	{
		g_blastFindHookInstalled = InstallBlastFindHook();
	}
	// ===== 磁力菇跳过防爆门 hook（0x4620BD）延迟安装 =====
	// 需求：**磁力菇不能吸防爆门的任何防具**（铁门/铁桶都不可吸）。找目标循环里
	// 防爆门直接跳过 → 磁力菇找别的目标或待机，防爆门完全免疫磁力菇
	if (!g_blastMagnetBlockInstalled && (g_blastHooksReady || g_blastHooksGivenUp))
	{
		g_blastMagnetBlockInstalled = InstallBlastMagnetBlockHook();
	}
	// ===== 大嘴花跳过撕咬动画 hook（0x461490）延迟安装 =====
	// ★崩溃根因修复：撕咬动画段 call 0x515020 在防爆门场景破坏 ebp（tdEbp=0x28 铁证）
	// → 防爆门直接跳 0x4614DC 伤害段（跳过 0x515020），伤害/状态不变
	if (!g_blastSkipAnimInstalled && (g_blastHooksReady || g_blastHooksGivenUp))
	{
		g_blastSkipAnimInstalled = InstallBlastSkipAnimHook();
	}
	// ===== 大嘴花拦截撕咬动画 call hook（0x4614D7）延迟安装 =====
	// ★v5.3 双保险：skipanim 若未拦截（tdEbp 仍 0x28），这里直接拦 call 0x515020 本身
	if (!g_blastSkipCallInstalled && (g_blastHooksReady || g_blastHooksGivenUp))
	{
		g_blastSkipCallInstalled = InstallBlastSkipCallHook();
	}
	// ★大嘴花 5阶巨人 + 防爆门统一由 0x461447 hook（InstallBlastChomperHook）BLOCKED 处理，
	//   不再单独 hook 0x461456/0x4614DC。

	// ===== 大嘴花（Chomper）：等阶机制每帧轮询（血量上限 + 消化计时覆盖 + 消化完成回血）=====
	CRASH_STEP("chomper");
	ChomperFrame(boardAddress);

	// ===== 墓碑吞噬者：吞噬墓碑检测 + 0~3 阶产出（经验包/冷却/僵尸/卡片）=====
	CRASH_STEP("gravebuster");
	GbFrame(boardAddress);

	// ===== 撑杆司令：皮肤贴图（body1/outerarm_upper/outerarm_upper2）延迟加载 =====
	// __try 放在独立函数 LoadCommanderSkinImages 里（onGameObjectsUpdate 含大量
	// std::vector/map 局部对象，直接内联 __try 会触发 MSVC C2712）
	if (!g_cmdrSkinImageLoaded && ImageLoadRetryAllowed(3))
	{
		g_cmdrSkinImageLoaded = true;
		LoadCommanderSkinImages();
	}

	// ===== 撑杆司令：每帧给司令应用皮肤贴图（幂等）=====
	CRASH_STEP("commanderskin");
	// 动画实例随状态切换（持杆/跳跃/无杆）可能重建，每帧重设保证始终生效；
	// 普通撑杆（非司令）不在此集合，保持原版贴图。
	if ((g_cmdrSkinImages[0] || g_cmdrSkinImages[1] || g_cmdrSkinImages[2] || g_cmdrSkinImages[3])
		&& !g_commanderZombies.empty())
	{
		PVZ::Board board(boardAddress);
		if (board.GetBaseAddress())
		{
			auto zombies = board.GetAllZombies();
			for (auto& z : zombies)
			{
				if (z.NotExist)
					continue;
				int zaddr = z.GetBaseAddress();
				if (!zaddr)
					continue;
				int fullId = MemSafeRead<int>(zaddr + 0x158);
				if (g_commanderZombies.count(fullId) == 0)
					continue;
				ApplyCommanderSkin(zaddr);
			}
		}
	}

	// ===== 豌豆射手 5 阶骑士皮肤：贴图延迟加载 + 每帧幂等应用 =====
	// （两轨已由 patch_reanim.py 写进 PeaShooterSingle.reanim；轨道缺失时本段自动静默）
	CRASH_STEP("peashooter:t5skin");
	if (!g_pst5SkinImgLoaded && g_pst5SkinImgTries < 600)
	{
		g_pst5SkinImgTries++;
		if (g_pst5SkinImg[0] && g_pst5SkinImg[1] && g_pst5SkinImg[2])
			g_pst5SkinImgLoaded = true;
		else
			LoadPeaShooterT5SkinImages();
	}
	// ★ v7：安装"绘制期应用"钩子（Reanimator::Draw 0x472E40 入口）。
	//   帧首那段照旧保留（双保险）；绘制期挂钩子才是"写到被绘制的那个对象上"的保证。
	//   向日葵 3 阶皮肤复用同一个钩子 → 任一皮肤开着就要装上。
	if (!g_pst5DrawHookInstalled && (g_pst5SkinEnabled || g_sunf3SkinEnabled)) InstallPst5DrawHook();
	PeaShooterT5SkinFrame(boardAddress);

	// ===== 向日葵 3 阶「皇冠 + 权杖」皮肤：贴图延迟加载 + 每帧幂等应用 =====
	// （两轨已由 patch_sunflower_skin.py 写进 SunFlower.reanim；轨道缺失时本段自动静默）
	CRASH_STEP("sunflower:t3skin");
	if (!g_sunf3ImgLoaded && g_sunf3ImgTries < 600)
	{
		g_sunf3ImgTries++;
		if (g_sunf3Img[0] && g_sunf3Img[1] && g_sunf3Img[2])
			g_sunf3ImgLoaded = true;
		else
			LoadSunFlowerT3SkinImages();
	}
	SunFlowerT3SkinFrame(boardAddress);

	// ===== 火炬树桩 清理前一帧的刚过火标记 =====
	CRASH_STEP("torchwood:clear");
	g_justFiredProjectiles.clear();

	// ===== 双发射手 延迟减速执行 =====
	CRASH_STEP("repeater:icefire");
	// 冰火豌豆的减速必须等火豌豆defrost先完成，故延迟到下一帧
	for (auto& pair : g_pendingIceFireDecelerates)
	{
		int zombieAddr = pair.first;
		int duration = pair.second;
		PVZ::Zombie zombie(zombieAddr);
		if (!zombie.NotExist)
			zombie.Decelerate(duration);
	}
	g_pendingIceFireDecelerates.clear();

	// ===== 向日葵5阶升级执行 =====
	CRASH_STEP("sunflower:upgrade");
	if (g_upgradeSunflowerAddr != 0)
	{
		PVZ::Plant oldPlant(g_upgradeSunflowerAddr);
		if (oldPlant.isValid() && !oldPlant.NotExist)
		{
			int row = g_upgradeRow;
			int col = g_upgradeCol;
			int exp = g_upgradeExp;

			// 清空经验防止 onPlantRemove 分配出去
			g_plantExperience[g_upgradeSunflowerAddr] = 0;

			// 移除向日葵
			oldPlant.Remove();

			// 创建双子向日葵
			PVZ::Plant newPlant = Creator::CreatePlant(SeedType::TwinSunflower, row, (byte)col);
			int newAddr = newPlant.GetBaseAddress();
			if (newAddr)
			{
				g_plantExperience[newAddr] = exp;
			}
		}

		g_upgradeSunflowerAddr = 0;
		g_upgradeRow = -1;
		g_upgradeCol = -1;
		g_upgradeExp = 0;
	}

	// 冰锥加速：测量游戏实际移动距离，额外补 50%（[3C]速度字段创建时为0，不可用）
	for (auto addr : g_snowPeaIcicleProjectiles)
	{
		PVZ::Projectile icicle(addr);
		if (icicle.NotExist) continue;
		float x = icicle.X;
		auto it = g_iciclePrevX.find(addr);
		if (it != g_iciclePrevX.end())
		{
			float moved = x - it->second;      // 游戏本帧净移动距离
			if (moved > 0.05f)
				icicle.X = x + moved * 0.5f;   // 额外补 50% → 合计 1.5 倍
		}
		g_iciclePrevX[addr] = x;               // 记录未加额外前的坐标
	}

	// ===== 路灯花特殊机制 =====
	CRASH_STEP("plantern");
	{
		PVZ::Board board(boardAddress);
		// 仅在迷雾关卡生效
		if (board.GetBaseAddress() && board.LevelScene == SceneType::Fog)
		{
			auto plants = board.GetAllPlants();

			for (auto& plant : plants)
			{
				if (plant.Type != SeedType::Plantern)
					continue;
				if (!plant.isValid() || plant.NotExist)
					continue;

				int plantAddr = plant.GetBaseAddress();
				int row = (int)plant.Row;
				int col = (int)plant.Column;

				// 获取等阶
				int exp = 0;
				auto expIt = g_plantExperience.find(plantAddr);
				if (expIt != g_plantExperience.end())
					exp = expIt->second;
				int tier = GetPlantTier((int)SeedType::Plantern, exp);

				// --- 1-4阶：开雾范围扩展 ---
				// 原版路灯花开雾范围: 左右各3格，上下各1格
				// 1阶: +1右 | 2阶: +1上+1下 | 3阶: +1右 | 4阶: +1上+1下
				// 雾数组位于 Board+0x4C8（指针表: 4C8~5C0\\雾的浓度），列优先 9列×7行
				if (tier >= 1)
				{
					int leftExt = 3;
					int rightExt = 3;
					int upExt = 1;
					int downExt = 1;

					rightExt += 1;                 // 1阶: 向右+1
					if (tier >= 2) { upExt += 1; downExt += 1; }  // 2阶: 上下+1
					if (tier >= 3) rightExt += 1;                  // 3阶: 向右+1
					if (tier >= 4) { upExt += 1; downExt += 1; }  // 4阶: 上下+1

					int cStart = col - leftExt;
					if (cStart < 0) cStart = 0;
					int cEnd = col + rightExt;
					if (cEnd > 8) cEnd = 8;
					int rStart = row - upExt;
					if (rStart < 0) rStart = 0;
					int rEnd = row + downExt;
					if (rEnd > 5) rEnd = 5;

					for (int r = rStart; r <= rEnd; r++)
						for (int c = cStart; c <= cEnd; c++)
							MemSafeWrite<int>(boardAddress + 0x4C8 + 0x1C * c + 4 * r, 0);
				}

				// --- 5阶：每12秒给3x3范围内的植物回复50血量 ---
				if (tier >= 5)
				{
					int nowTime = board.PlayingTime;
					auto healIt = g_planternHealTimers.find(plantAddr);
					int lastHeal = (healIt != g_planternHealTimers.end())
						? healIt->second : (nowTime - 1200);

					if (nowTime - lastHeal >= 1200) // 12秒 = 1200厘秒
					{
						g_planternHealTimers[plantAddr] = nowTime;

						for (auto& target : plants)
						{
							if (!target.isValid() || target.NotExist)
								continue;
							int tRow = (int)target.Row;
							int tCol = (int)target.Column;

							if (abs(tRow - row) <= 1 && abs(tCol - col) <= 1)
							{
								int hp = target.Hp;
								int maxHp = target.MaxHp;
								int newHp = hp + 50;
								if (newHp > maxHp) newHp = maxHp;
								target.Hp = newHp;
							}
						}
					}
				}
			}
		}
	}

	// ===== 火炬树桩 二次过火检测 =====
	CRASH_STEP("torchwood:refire");
	// 已过火的子弹（弱火→火、火→炎）再次经过火炬树桩时升级
	// 原生火豌豆（如双发射手火豌豆）经过高等级火炬也会升级
	{
		PVZ::Board board(boardAddress);
		if (board.GetBaseAddress())
		{
			auto projectiles = board.GetAllProjectile();
			auto allPlants = board.GetAllPlants();

			for (auto& proj : projectiles)
			{
				if (proj.NotExist) continue;
				int projAddr = proj.GetBaseAddress();
				int projRow = (int)proj.Row;
				float projX = proj.X;

				// 刚被 onPeaOnFire 处理过，跳过
				if (g_justFiredProjectiles.find(projAddr) != g_justFiredProjectiles.end())
					continue;

				// 只处理火豌豆类型或已有过火状态的子弹
				bool isFirePea = (proj.Type == ProjectileType::FirePea);
				auto stateIt = g_projectileFireStates.find(projAddr);
				if (!isFirePea && stateIt == g_projectileFireStates.end())
					continue;

				// 获取或初始化过火状态
				ProjectileFireState fs;
				bool hasState = (stateIt != g_projectileFireStates.end());
				if (hasState)
					fs = stateIt->second;
				else
				{
					// 原生火豌豆（如双发射手），初始化为 fireLevel=2
					fs.fireLevel = 2;
					fs.damage = 40;
					fs.noDefrost = false;
					fs.lastTorchCol = -1;
				}

				// 已经是炎豌豆（最高级），不再升级
				if (fs.fireLevel >= 3)
					continue;

				// 找同行火炬树桩（不同列，排除刚经过的那个）
				int bestTier = -1;
				int bestCol = -1;
				for (auto& plant : allPlants)
				{
					if (plant.Type != SeedType::Torchwood) continue;
					if ((int)plant.Row != projRow) continue;
					if (plant.NotExist) continue;

					int plantCol = (int)plant.Column;
					// 跳过同一列的火炬（刚经过的）
					if (plantCol == fs.lastTorchCol) continue;

					int plantAddr = plant.GetBaseAddress();
					auto expIt = g_plantExperience.find(plantAddr);
					int tier = 0;
					if (expIt != g_plantExperience.end())
						tier = GetPlantTier((int)SeedType::Torchwood, expIt->second);

					float torchX = (float)board.GridToXPixel(projRow, plantCol) + 40.0f;
					if (projX >= torchX - 30.0f && projX <= torchX + 50.0f)
					{
						if (tier > bestTier)
						{
							bestTier = tier;
							bestCol = plantCol;
						}
					}
				}

				if (bestTier < 0) continue;

				// 升级逻辑
				bool upgraded = false;

				if (fs.fireLevel == 1)
				{
					// 弱火豌豆 → 火豌豆
					fs.fireLevel = 2;
					fs.damage = (bestTier >= 4) ? 50 : 40;
					fs.noDefrost = (bestTier >= 5);
					fs.lastTorchCol = bestCol;
					upgraded = true;
				}
				else if (fs.fireLevel == 2 && bestTier >= 3)
				{
					// 火豌豆 → 炎豌豆（3阶+）
					fs.fireLevel = 3;
					fs.damage = (bestTier >= 4) ? 80 : 60;
					fs.noDefrost = (bestTier >= 5);
					fs.lastTorchCol = bestCol;
					upgraded = true;
				}
				else if (fs.fireLevel == 2 && bestTier >= 5)
				{
					// 5阶但不满足3阶升级条件（不可能，5>=3），保留作为安全分支
					fs.noDefrost = true;
					fs.lastTorchCol = bestCol;
					upgraded = true;
				}

				if (upgraded)
				{
					g_projectileFireStates[projAddr] = fs;
					// 染色标记同步：弱火(1)=淡橙黄、火(2)=不染色、炎(3)=炽红
					int colorMark = (fs.fireLevel == 1) ? 1 : ((fs.fireLevel == 3) ? 2 : 0);
					SetPeaColorMark(projAddr, colorMark);
				}
			}
		}
	}

	// ===== 裂荚豌豆首火兜底 =====
	CRASH_STEP("splitpea:firstfire");
	// 原生过火判定（hook 0x4606B7）只覆盖向右飞的普通豌豆；裂荚向左子弹（[proj+0x80]==92）
	// 和反弹后的子弹（==93）若是普通豌豆且尚未过火，在此按位置窗口兜底首火。
	// 逻辑同 onPeaOnFire（等阶伤害 30/40/50）+ onSnowPeaFire 的原生 OnFire 调用方式：
	// 预写 [proj+0x78]=0x5A 且 eax=0x5A5A5A5A，确保 OnFire 入口 cmp 不相等、不提前返回。
	// ★ 反弹子弹二次穿过同一火炬的"升级"由上方二次过火扫描处理，这里只管首火（Type==Pea）。
	// ★ 原生已首火的子弹 Type 已是 FirePea，此处天然跳过，无双火。
	{
		PVZ::Board board(boardAddress);
		if (board.GetBaseAddress())
		{
			auto projectiles = board.GetAllProjectile();
			for (auto& proj : projectiles)
			{
				if (proj.NotExist) continue;
				if ((int)proj.Type != (int)ProjectileType::Pea) continue;
				int pAddr = proj.GetBaseAddress();
				if (!pAddr) continue;
				int mark = MemSafeRead<int>(pAddr + 0x80);
				if (mark != SPLIT_PEA_LEFT && mark != SPLIT_PEA_RIGHT && mark != SPLIT_PEA_LEFT_NB) continue;
				if (g_justFiredProjectiles.find(pAddr) != g_justFiredProjectiles.end()) continue;

				int torchCol = -1;
				int tier = FindTorchwoodTierForProjectile(pAddr, &torchCol);
				if (tier < 0) continue;

				// 首火：原生 OnFire（Type→FirePea + 火球贴图/音效/粒子）
				static DWORD g_spFireProj = 0;
				g_spFireProj = (DWORD)pAddr;
				MemSafeWrite<int>(pAddr + 0x78, 0x5A);
				__asm
				{
					mov ecx, dword ptr [g_spFireProj]
					mov eax, 0x5A5A5A5A
					mov ebx, 0x46ECB0
					call ebx
				}

				ProjectileFireState fs;
				fs.fireLevel = (tier >= 2) ? 2 : 1;
				fs.damage = (tier >= 2) ? ((tier >= 4) ? 50 : 40) : 30;
				fs.noDefrost = (tier >= 5);
				fs.lastTorchCol = torchCol;
				g_projectileFireStates[pAddr] = fs;
				g_justFiredProjectiles.insert(pAddr);
				// 染色标记：弱火(1)=淡橙黄，火(2)=不染色（[proj+0x8C]）
				SetPeaColorMark(pAddr, (fs.fireLevel == 1) ? 1 : 0);
			}
		}
	}

	// ===== 裂荚射手 3阶+ 向左子弹反弹 =====
	CRASH_STEP("splitpea:bounce");
	// 向左子弹（[proj+0x80]==92，运动类型6 X-=3.33/帧）碰到屏幕左边（X<=40）反弹：
	// 改运动类型为0（普通向右 X+=3.33/帧，速度一致），方向反转。
	// ★ 提前量：越界删除点在 X+row<=0（X<=-row~-5），40 远早于删除，安全。
	// ★ 飞行保护：初始 X 记录在 [proj+0x84]（onPlantAddProjectile 事件写入，零 map），
	//   必须确实向左飞行 ≥60px 才反弹——防止出生点已在 X<=40 的子弹（目标槽偏移残留）
	//   出生即反弹误判向右。
	// ★ 防重复：反弹后 [proj+0x80]=93（RIGHT），下一帧不再匹配 92，天然防重复。
	// ★★ 两次过火关键：反弹时清两级 lastTorchCol——
	//   1) [proj+0x78]=-1（原生"上一次穿过火炬列"，不清则原生判定跳过同一火炬）
	//   2) g_projectileFireStates 的 lastTorchCol=-1（自定义二次过火扫描的同列跳过依据）
	//   → 反弹回来的子弹可再次穿过同一火炬升级（弱火→火→炎）。
	{
		PVZ::Board board(boardAddress);
		if (board.GetBaseAddress())
		{
			auto projectiles = board.GetAllProjectile();
			for (auto& proj : projectiles)
			{
				if (proj.NotExist) continue;
				int pAddr = proj.GetBaseAddress();
				if (!pAddr) continue;
				if (MemSafeRead<int>(pAddr + 0x80) != SPLIT_PEA_LEFT) continue;
				float px = proj.X;
				float initX = MemSafeRead<float>(pAddr + 0x84);
				if (initX <= 0.0f) initX = px;   // 兜底：无记录时以当前位置为基准（不反弹）
				if (px <= 40.0f && (initX - px) >= 60.0f)
				{
					MemSafeWrite<int>(pAddr + 0x58, 0);   // 运动类型0 = 普通向右
					MemSafeWrite<int>(pAddr + 0x80, SPLIT_PEA_RIGHT);
					MemSafeWrite<int>(pAddr + 0x78, -1);  // 清原生 lastTorchCol
					MemSafeWrite<float>(pAddr + 0x68, 0.0f);  // 旋转复位（向右不镜像）
					auto fsIt = g_projectileFireStates.find(pAddr);
					if (fsIt != g_projectileFireStates.end())
						fsIt->second.lastTorchCol = -1;               // 清自定义 lastTorchCol
					// 诊断日志（验证后可移除）
					FILE* f = fopen("D:\\pvz_split_debug.txt", "a");
					if (f) { fprintf(f, "[bounce] proj=%08X initX=%.1f curX=%.1f type=%d\n", pAddr, initX, px, (int)proj.Type); fclose(f); }
				}
			}
		}
	}

	// ===== 裂荚左向火豌豆贴图镜像（④）：向左飞（92/94）旋转 180°，向右/反弹（93）恢复 0 =====
	CRASH_STEP("splitpea:mirror");
	// 仅火豌豆需要（普通豌豆贴图左右对称）；+0x68 旋转角度 / +0x6C 旋转速度（指针表实测）。
	// 每帧按标记强制写，贴图方向与飞行方向始终一致；旋转速度清 0 防原生累加漂移。
	{
		PVZ::Board board(boardAddress);
		if (board.GetBaseAddress())
		{
			auto projectiles = board.GetAllProjectile();
			for (auto& proj : projectiles)
			{
				if (proj.NotExist) continue;
				if ((int)proj.Type != (int)ProjectileType::FirePea) continue;
				int pAddr = proj.GetBaseAddress();
				if (!pAddr) continue;
				int mark = MemSafeRead<int>(pAddr + 0x80);
				if (mark != SPLIT_PEA_LEFT && mark != SPLIT_PEA_RIGHT && mark != SPLIT_PEA_LEFT_NB) continue;
				// 无条件每帧写：原生 SpinPea 更新在物体阶段会按 +0x6C 自旋累加 +0x68，
				// 条件写（cur!=want）会被下一帧累加覆盖 → 反弹弹贴图方向不变的用户实测 bug
				float want = (mark == SPLIT_PEA_RIGHT) ? 0.0f : 3.14159265f;
				MemSafeWrite<float>(pAddr + 0x68, want);
				MemSafeWrite<float>(pAddr + 0x6C, 0.0f);
			}
		}
	}

	// ===== 三线射手：普攻弹行号判定（95/96 交叉标记，写 DLL map）+ 大招状态机 =====
	CRASH_STEP("threepeater:rowmark");
	{
		// ① 普攻弹登记处理：[+0x1C] 行号 vs 植物行 → 上/下路交叉标记 + 轴Y（出生Y）+ 植物行
		//    （±θ 大招弹已由 TripleUltShoot 同步注入消费，数组里只剩普攻弹 mark==0）
		for (int i = 0; i < g_triplePendingCount; i++)
		{
			DWORD pa = g_triplePendingMarks[i].plant;
			DWORD pr = g_triplePendingMarks[i].proj;
			int mk = g_triplePendingMarks[i].mark;
			if (mk != 0) continue;          // 理论无残留（98/99 大招弹已同步消费），防御
			if (MemSafeRead<BYTE>(pr + 0x50)) continue;   // 子弹已移除
			if (MemSafeRead<int>(pa + 0x24) != (int)SeedType::Threepeater) continue;

			int exp = 0;
			auto eIt = g_plantExperience.find(pa);
			if (eIt != g_plantExperience.end()) exp = eIt->second;
			if (GetPlantTier((int)SeedType::Threepeater, exp) < 3) continue;

			int plantRow = MemSafeRead<int>(pa + 0x1C);
			int projRow = MemSafeRead<int>(pr + 0x1C);
			// 轴Y = 子弹出生 Y（原版三线三颗弹都从中路弹道出发，出生 1 帧内 Y≈中路弹道线；
			// 上下路子弹没有自己的"路"，都围绕此轴振动）
			float axisY = MemSafeRead<float>(pr + 0x34);
			if (projRow == plantRow - 1)
				g_tripleMark[pr] = { TRIPLE_UP, axisY, plantRow };
			else if (projRow == plantRow + 1)
				g_tripleMark[pr] = { TRIPLE_DOWN, axisY, plantRow };
			// projRow == plantRow → 中路弹，不标记直飞（即振动轴本身）
		}
		g_triplePendingCount = 0;

		// 清理已死亡子弹的 map 残留（防内存池复用误判）
		for (auto it = g_tripleMark.begin(); it != g_tripleMark.end(); )
		{
			if (MemSafeRead<BYTE>(it->first + 0x50))
				it = g_tripleMark.erase(it);
			else
				++it;
		}

		// ② 大招状态机（暂时禁用——大招弹平射问题未解，用户要求先注释）
		// 恢复时取消下方注释即可（开大判定在 onPlantAddProjectile 三线块内同步恢复）
		/*
		for (int i = 0; i < 24; i++)
		{
			if (g_tripleStates[i].plant == 0 || g_tripleStates[i].ultTicks <= 0) continue;
			DWORD pa = g_tripleStates[i].plant;
			// 植物被铲/死亡 → 立即终止大招（槽位回收）
			if (MemSafeRead<int>(pa + 0x24) != (int)SeedType::Threepeater
				|| MemSafeRead<BYTE>(pa + 0x141))
			{
				g_tripleStates[i].plant = 0;
				continue;
			}
			int t = --g_tripleStates[i].ultTicks;
			MemSafeWrite<int>(pa + 0x58, 400);   // 钉住普攻冷却（大招期间不普攻）
			if (t % 3 == 0)
			{
				TripleUltShoot(pa, g_tripleStates[i].row, t);
				TriplePlayShootSound();
			}
			if (t <= 0)
			{
				// 大招结束：写回等阶攻击冷却
				int exp2 = 0;
				auto eIt2 = g_plantExperience.find(pa);
				if (eIt2 != g_plantExperience.end()) exp2 = eIt2->second;
				int tier2 = GetPlantTier((int)SeedType::Threepeater, exp2);
				float ts2 = GetPlantAttackSpeed((int)SeedType::Threepeater, tier2);
				int cd2 = 150;
				if (ts2 > 0) cd2 = (int)(150 * ts2 / 1.5f);
				if (cd2 <= 0) cd2 = 1;
				MemSafeWrite<int>(pa + 0x58, cd2);
				g_tripleStates[i].plant = 0;
			}
		}
		*/
	}

	// ===== 三线射手：正弦弹道（YSpeed 积分式，Y = 轴Y ± A·sin(ω·t)）+ 行号更新 =====
	CRASH_STEP("threepeater:sin");
	// ★★ 必须用 YSpeed 式，不能直接写 Y[+0x34]！实测直接写 Y（+清 YSpeed）→ 原生豌豆
	//   每帧 YSpeed 积分后做一致性检查，发现 Y 被外部改写 → 固定时间点移除子弹
	//   （96 下路弹 t=12 / 95 上路弹 t=66 + 命中动画 + 无僵尸无墓碑）。v2/v3 YSpeed 式能飞。
	// ★ YSpeed = ∓A·ω·cos(ωt)（位置 Y=轴Y∓A·sin(ωt) 的导数），原生 Y+=YSpeed 积分：
	//   95 上路弹：YSpeed=-A·ω·cos → 位置轴Y-A·sin（t=0 在中路轴，先向上，扫过上中下）
	//   96 下路弹：YSpeed=+A·ω·cos → 轴Y+A·sin（先向下）
	//   A=场景行高（85/100，振动顶点正好到上/下路中心线），A·ω≈5
	// ★ 不写 Y/ImageY/不清 YSpeed（全交原生积分），零外部坐标改写 = 零早死
	// 98/99: 大招弹（大招暂时禁用；保留代码供恢复）
	// 行号经 TriplePixelToGridY 重算（振动中正确索敌/命中）
	{
		PVZ::Board board(boardAddress);
		if (board.GetBaseAddress())
		{
			int scene = MemSafeRead<int>(boardAddress + 0x554C);
			float amp = (scene == 2 || scene == 3) ? 85.0f : 100.0f;   // 泳池/迷雾 六行 85px，其余 100px
			int lastRow = (scene == 2 || scene == 3) ? 5 : 4;          // 泳池/迷雾 六行
			float speedAmp = amp * TRIPLE_SIN_W;                       // A·ω ≈ 5
			auto projectiles = board.GetAllProjectile();
			for (auto& proj : projectiles)
			{
				if (proj.NotExist) continue;
				int pAddr = proj.GetBaseAddress();
				if (!pAddr) continue;
				auto mit = g_tripleMark.find(pAddr);
				if (mit == g_tripleMark.end()) continue;
				int mark = mit->second.mark;
				int t = MemSafeRead<int>(pAddr + 0x60);   // ExistedTime（原生每帧+1）
				if (mark == TRIPLE_UP || mark == TRIPLE_DOWN)
				{
					float w = TRIPLE_SIN_W * (float)t;
					float vy = speedAmp * cosf(w);
					if (mark == TRIPLE_UP) vy = -vy;              // 上路弹反相位（位置先向上）
					// ★ 边路单侧折叠：第一行三线的下路弹（96）、最下一行三线的上路弹（95），
					//   正弦波折到单侧（Y=轴Y±A·|sin(ωt)|，vy 乘 sign(sin)）——
					//   上面弹道部分翻到下面/下面翻到上面，子弹恒不越过中路轴（用户新方案）。
					//   中间行不折叠，保持完整上下振动。
					int plantRow3 = mit->second.plantRow;
					if ((mark == TRIPLE_DOWN && plantRow3 == 0) ||
						(mark == TRIPLE_UP && plantRow3 == lastRow))
						vy = (sinf(w) >= 0.0f) ? vy : -vy;
					MemSafeWrite<float>(pAddr + 0x40, vy);
				}
				else
				{
					// 98/99 大招弹（大招暂时禁用，无子弹会带此标记；保留代码供恢复）
					float base = MemSafeRead<float>(pAddr + 0x40);
					float parity = ((t / 50) % 2 == 0) ? 1.0f : -1.0f;   // 每 50 帧翻转垂直速度
					MemSafeWrite<float>(pAddr + 0x40, base * parity);
				}
				int newRow = TriplePixelToGridY((int)boardAddress, (int)proj.X, (int)(proj.Y + 40.0f));
				if (newRow >= 0 && newRow <= 5)
					MemSafeWrite<int>(pAddr + 0x1C, newRow);
			}
		}
	}

	// ===== 三线射手：状态清理 =====
	CRASH_STEP("threepeater:cleanup");
	// 大招/登记状态均在处理块内维护（ultTicks 驱动）；此处仅清理失效植物槽位
	// （铲除/死亡/内存池复用），防止 ultTicks>0 的死地址被状态机持续写内存
	{
		for (int i = 0; i < 24; i++)
		{
			if (g_tripleStates[i].plant == 0) continue;
			DWORD pa = g_tripleStates[i].plant;
			if (!MemSafeRead<int>(pa) ||
				MemSafeRead<BYTE>(pa + 0x141) ||
				MemSafeRead<int>(pa + 0x24) != (int)SeedType::Threepeater)
			{
				g_tripleStates[i].plant = 0;   // NotExist(0x141) 或类型不符 → 清理
				continue;
			}
		}
	}

	// ===== 裂荚连射队列补发（③连射不堆叠）：每 28 tick 出队一颗（双发射手原生节奏） =====
	CRASH_STEP("splitpea:queue");
	// SplitPeaShoot 当场只发第一颗，其余入队；这里按固定间隔逐颗补发（调用原生
	// 0x466E00 与首颗同路径，事件 hook 正常标记方向/兜底首火）。
	{
		if (g_spQueueHead != g_spQueueTail)
		{
			if (g_spQueueTimer > 0)
				g_spQueueTimer--;
			else
			{
				SplitPeaShot s = g_spShotQueue[g_spQueueHead];
				g_spQueueHead = (g_spQueueHead + 1) % 128;
				// 植物已铲/已亡/非裂荚（内存池复用防护）则丢弃该发
				PVZ::Plant plant(s.plant);
				if (plant.isValid() && !plant.NotExist &&
					MemSafeRead<int>(s.plant + 0x24) == (int)SeedType::SplitPea)
				{
					int row = MemSafeRead<int>(s.plant + 0x1C);
					g_splitPeaPendingDir = s.dir;
					fnSplitShoot((int)s.plant, 0, row, s.dir);
					g_splitPeaPendingDir = -1;
				}
				// 间隔 = 双发射手原生节奏（Gatling 触发点 126/98/70/42，固定差 28 tick）
				g_spQueueTimer = 28;
			}
		}
	}

	// ===== 机枪射手：经验溢出→大招能量 + 大招状态机 + 大招弹行号重算 =====
	CRASH_STEP("gatling:ult");
	{
		PVZ::Board board(boardAddress);
		if (board.GetBaseAddress())
			GatlingFrame((int)boardAddress);
	}

	// ===== 小喷菇集群更新 =====
	CRASH_STEP("puffshroom");
	{
		PVZ::Board board(boardAddress);
		if (board.GetBaseAddress())
		{
			int nowTime = board.PlayingTime;
			std::vector<int> deadCellKeys;

			for (auto& pair : g_puffClusters)
			{
				int cellKey = pair.first;
				auto& cluster = pair.second;

				// --- 1. 首领（plants[0]）死亡：提拔下一个为新的首领 ---
				if (cluster.plants[0] != 0)
				{
					PVZ::Plant leader(cluster.plants[0]);
					if (!leader.isValid() || leader.NotExist)
					{
						// 找第一个存活的 plants[1-4] 提拔
						int promoteIdx = -1;
						for (int i = 1; i < 5; i++)
						{
							if (cluster.plants[i] != 0)
							{
								PVZ::Plant candidate(cluster.plants[i]);
								if (candidate.isValid() && !candidate.NotExist)
								{
									promoteIdx = i;
									break;
								}
							}
						}

						if (promoteIdx >= 0)
						{
							DWORD newLeader = cluster.plants[promoteIdx];
							// 新首领从 g_puffToCell 中移除（不再是"分身"）
							g_puffToCell.erase(newLeader);
							// 提拔到 plants[0]
							cluster.plants[0] = newLeader;
							cluster.plants[promoteIdx] = 0;

							// 把死首领的经验转移给新首领
							// 死首领的经验已被 onPlantRemove 保存到 g_lastDeathRow/g_lastDeathExp
							if (g_lastDeathRow >= 0)
							{
								PVZ::Plant nl(newLeader);
								if ((int)nl.Row == g_lastDeathRow)
								{
									int oldExp = 0;
									auto existIt = g_plantExperience.find(newLeader);
									if (existIt != g_plantExperience.end())
										oldExp = existIt->second;
									g_plantExperience[newLeader] = oldExp + g_lastDeathExp;
									// 清除死亡分配标记，防止 onDrawExpUI 再分发
									g_lastDeathRow = -1;
									g_lastDeathExp = 0;
								}
							}
						}
					}
				}

				// --- 2. 清理已死但还占着槽位的 plants[1-4] ---
				for (int i = 1; i < 5; i++)
				{
					if (cluster.plants[i] == 0) continue;
					PVZ::Plant p(cluster.plants[i]);
					if (!p.isValid() || p.NotExist)
					{
						g_puffToCell.erase(cluster.plants[i]);
						cluster.plants[i] = 0;
					}
				}

				// --- 3. 首领也死了且无替补 → 集群彻底消亡 ---
				if (cluster.plants[0] != 0)
				{
					PVZ::Plant leader(cluster.plants[0]);
					if (!leader.isValid() || leader.NotExist)
					{
						g_puffToCell.erase(cluster.plants[0]);
						cluster.plants[0] = 0;
					}
				}

				if (cluster.GetCount() == 0)
				{
					deadCellKeys.push_back(cellKey);
					continue;
				}

				// --- 4. 同步最大数量 ---
				if (cluster.plants[0] != 0)
				{
					int exp = 0;
					auto expIt = g_plantExperience.find(cluster.plants[0]);
					if (expIt != g_plantExperience.end())
						exp = expIt->second;
					int tier = GetPlantTier((int)SeedType::Puffshroom, exp);
					cluster.maxCount = GetPuffMaxCount(tier);
				}

				// --- 4.5 咖啡豆唤醒检测：任一被唤醒则全格苏醒 ---
				if (cluster.plants[0] != 0 && !cluster.clusterAwake)
				{
					PVZ::Plant leader(cluster.plants[0]);
					if (leader.isValid() && !leader.NotExist && !leader.Sleeping)
					{
						// 首领被咖啡豆唤醒 → 唤醒所有分身
						for (int i = 1; i < 5; i++)
						{
							if (cluster.plants[i] == 0) continue;
							PVZ::Plant p(cluster.plants[i]);
							if (p.isValid() && !p.NotExist && p.Sleeping)
								p.SetSleeping(false);
						}
						cluster.clusterAwake = true;
					}
				}
				// 也检查分身中是否有被单独唤醒的
				if (!cluster.clusterAwake)
				{
					for (int i = 1; i < 5; i++)
					{
						if (cluster.plants[i] == 0) continue;
						PVZ::Plant p(cluster.plants[i]);
						if (p.isValid() && !p.NotExist && !p.Sleeping)
						{
							// 有分身被唤醒了 → 全格唤醒
							cluster.clusterAwake = true;
							break;
						}
					}
					if (cluster.clusterAwake)
					{
						// 唤醒其他所有
						for (int i = 0; i < 5; i++)
						{
							if (cluster.plants[i] == 0) continue;
							PVZ::Plant p(cluster.plants[i]);
							if (p.isValid() && !p.NotExist && p.Sleeping)
								p.SetSleeping(false);
						}
					}
				}

				int totalCount = cluster.GetCount();

				// --- 5. 定时生成额外小喷菇（填充 plants[1-4] 的低编号空位）---
				if (totalCount < cluster.maxCount && (nowTime - cluster.lastSpawnTime) >= 3000)
				{
					// 必须有一个有效的首领才能生成
					if (cluster.plants[0] == 0) continue;
					PVZ::Plant leader(cluster.plants[0]);
					if (!leader.isValid() || leader.NotExist) continue;

					int emptySlot = cluster.FindEmptySlot();
					if (emptySlot < 0 || emptySlot > 4) continue;

					int row = (int)leader.Row;
					int col = (int)leader.Column;

					// 标记，让 onPlantCreate 跳过初始化
					g_creatingExtraPuff = true;

					PVZ::Plant newPlant = Creator::CreatePlant(
						SeedType::Puffshroom, row, (byte)col);
					DWORD newAddr = newPlant.GetBaseAddress();

					if (!newAddr)
					{
						g_creatingExtraPuff = false;
					}
					else
					{
						// 设置偏移和图层
						int offsetIdx = emptySlot - 1; // plants[1-4] 对应 PUFF_CLONE_OFFSETS[0-3]
						if (offsetIdx >= 0 && offsetIdx < 4)
						{
							const auto& off = PUFF_CLONE_OFFSETS[offsetIdx];
							newPlant.ImageXOffset = off.dx;
							newPlant.ImageYOffset = off.dy;
							newPlant.Layer = leader.Layer + off.layerDelta;
						}

						cluster.plants[emptySlot] = newAddr;
						g_puffToCell[newAddr] = cellKey;

						// 如果本格已唤醒，新生成的小喷菇也直接清醒
						if (cluster.clusterAwake)
							newPlant.SetSleeping(false);
					}

					cluster.lastSpawnTime = nowTime;
				}
			}

			// 清理死亡集群
			for (int ck : deadCellKeys)
				g_puffClusters.erase(ck);
		}
	}

	// ===== 胆小菇缩头 → 重置为初始攻速 / T5最快攻速手动开火 =====
	CRASH_STEP("scaredyshroom");
	{
		PVZ::Board board(boardAddress);
		int nowTime = board.PlayingTime;
		auto plants = board.GetAllPlants();
		auto zombies = board.GetAllZombies();
		for (auto& plant : plants)
		{
			if (plant.Type != SeedType::Scaredyshroom)
				continue;
			DWORD addr = plant.GetBaseAddress();
			if (!plant.isValid() || plant.NotExist)
				continue;

			auto stateIt = g_scaredyStates.find(addr);
			if (stateIt == g_scaredyStates.end())
				continue;
			ScaredyState& st = stateIt->second;

			// ===== 极快攻速吞子弹修复：缩放 ShootingCountdown(0x90) =====
			// !! 必须在缩头判断【之前】：吞子弹发生在正常射击时，而非缩头时
			// 反汇编确认(1.0.0.1051)：
			//   FindTargetAndFire 0x45F19C: cmp type,0xd → 写 [esi+0x90]=0x19(25) 后 ret（此时不开火）
			//   UpdateShooting   0x464A8F: [edi+0x90] -= 1；==1 时 → 0x464BC5 call 0x466e00 才开火
			// 攻速过快时 +90 还没减到 1，ShootOrProductCountdown 已到期并再次 FindTargetAndFire
			// 把 +90 重置回 25 → 永远到不了 1 → 只播动画不出子弹（原地抖动）。
			// 参考 Hathing 机枪射手方案：+90 × 攻击间隔/150，动画速率 × 150/攻击间隔。
			int intervalCs = (int)(st.currentInterval + 0.5f);
			if (intervalCs > 0 && intervalCs < SCAREDY_BASE_INTERVAL_CS)
			{
				int shooting = plant.ShootingCountdown;
				// 值变大 = FindTargetAndFire 刚写入新的射击动画倒计时
				if (shooting > st.prevShootingCD && shooting > 1)
				{
					int scaled = (int)(shooting * intervalCs / (float)SCAREDY_BASE_INTERVAL_CS + 0.5f);
					if (scaled < 2) scaled = 2;   // 至少2：保证能递减到1触发开火
					if (scaled < shooting)
					{
						plant.ShootingCountdown = scaled;
						shooting = scaled;
						// 注：不缩放动画速率（anim.Speed）——让射击片段按自然速度播完整甩头，
						//     只缩 +90 防吞子弹；若视觉仍不对轴再评估加回
					}
				}
				st.prevShootingCD = shooting;
			}
			else
			{
				st.prevShootingCD = plant.ShootingCountdown;
			}

			// ===== 以下仅处理缩头状态 =====
			int pstate = (int)plant.State;
			if (pstate != PlantState::SCAREDYSHROOM_SCARED &&
			    pstate != PlantState::SCAREDYSHROOM_SCARED_IDLE)
				continue;

			int exp = 0;
			auto expIt = g_plantExperience.find(addr);
			if (expIt != g_plantExperience.end())
				exp = expIt->second;
			int tier = GetPlantTier((int)SeedType::Scaredyshroom, exp);

			float minInterval5 = GetPlantAttackSpeed((int)SeedType::Scaredyshroom, 5) * 100.0f;
			bool atMaxSpeed = (tier >= 5 && st.currentInterval <= minInterval5 + 0.1f);

			if (atMaxSpeed)
			{
				// T5最快攻速: 不重置间隔，手动开火维持攻击
				if (st.lastManualShootTime == 0)
					st.lastManualShootTime = nowTime - (int)(st.currentInterval + 0.5f);

				int elapsedMs = (nowTime - st.lastManualShootTime) * 10;  // cs→ms
				int intervalMs = (int)(st.currentInterval * 10 + 0.5f);    // cs→ms
				if (elapsedMs >= intervalMs)
				{
					// 找同行最近僵尸
					int plantRow = (int)plant.Row;
					int bestZombieIdx = -1;
					int bestDist = 99999;
					for (auto& z : zombies)
					{
						if ((int)z.Row != plantRow) continue;
						if (z.NotExist) continue;
						int dist = (int)z.X;
						if (dist < bestDist) { bestDist = dist; bestZombieIdx = (int)z.Index; }
					}
					if (bestZombieIdx >= 0)
					{
						plant.Shoot(MotionType::Track, bestZombieIdx);
						st.lastManualShootTime = nowTime;
					}
				}
			}
			else
			{
				// 非T5或未达最快攻速：缩头 → 重置为初始攻速
				float initialInterval = (tier >= 3) ? 150.0f : 220.0f;
				st.currentInterval = initialInterval;
				st.lastAttackTime = 0;
			}
		}
	}

	// ===== 卷心菜投手 T5 弹射结算（延迟一帧，毒爆/西瓜溅射同款安全模式）=====
	// ★ 纯物理弹射（2026-09-09 二次定稿）：不索敌、不找"下一个僵尸"，命中后按物理定律反弹——
	//   纵向速度分量反向 × 动量缩放系数，水平速度同系数缩小（总动量等比缩小）。
	//   原生 466E00 仅为创建宿主（必须要一个僵尸参数才能造弹），创建后轨迹三件套全部
	//   覆写为本帧物理量 → 宿主僵尸完全不参与瞄准；伤害/经验归属走原生路径。
	// 弹射不消耗植物攻击冷却（发射函数本身不动 [+0x58]，散射的冷却补偿只在散射时做）
	if (g_cabbageBounceCount > 0)
	{
		for (int bi = 0; bi < g_cabbageBounceCount; bi++)
		{
			CabbageBounceReq& rq = g_cabbageBounceQ[bi];
			// 发射植物已死亡/被铲 → 弹射作废
			if (!rq.plant || MemSafeRead<BYTE>(rq.plant + 0x141))
				continue;
			DWORD bAddr = MemSafeRead<int>(rq.plant + 4);
			if (!bAddr) continue;
			// 找同行任意存活僵尸作创建宿主（优先命中点后方最近；纯占位，不参与瞄准）
			PVZ::Board bounceBoard(bAddr);
			auto bzAll = bounceBoard.GetAllZombies();
			int bestIdx = -1;
			float bestX = 0.0f;
			for (auto& z : bzAll)
			{
				if (z.NotExist) continue;
				if ((int)z.Row != rq.row) continue;
				if (z.Hypnotized) continue;
				if (!z.EffectedBy(PVZ::DRF_ALL, false)) continue;
				float zx = z.X;
				if (bestIdx < 0
					|| (zx > rq.x && (bestX <= rq.x || zx < bestX))
					|| (zx <= rq.x && bestX <= rq.x && zx > bestX))
				{
					bestIdx = (int)z.Index; bestX = zx;
				}
			}
			if (bestIdx < 0) continue;      // 同行无存活僵尸 → 无创建宿主，弹射作废
			PVZ::Zombie bz(bestIdx);
			if (!bz.GetBaseAddress()) continue;
			// ★ 物理量：纵向反向 + 总动量等比缩小。缩放系数 0.685 使典型落速(~7)反弹
			//   峰值 ≈ (7×0.685)²/0.23 ≈ 100px（与上一版定稿观感一致）
			float k = 0.685f;
			float iv = rq.vel;              // 命中瞬间垂直速度（正=下落）
			if (iv < 0.3f) iv = 4.5f;       // 撞在上升段/近顶点（下沉量不足）→ 用典型落速
			if (iv > 15.0f) iv = 15.0f;     // 钳制异常
			float nv = -iv * k;             // 反弹后垂直速度（负=上升）；命中时若在上升段则为正=自然下坠
			float nx = rq.xs * k;           // 水平速度同系数缩小
			if (nx < 0.5f) nx = 0.5f;       // 水平至少向前爬行
			// ★ 出生点：命中点右移20px、上移110px（普通僵尸躯干高度，视觉=从僵尸身上弹起）。
			//   原生 Fire 出生点由植物 ImageX/ImageY 推导（出生x=ImageX+0x19、出生y=ImageY-0x2E）
			//   → 发射前临时瞬移，发射完立即还原（同一 C++ 同步段，无渲染穿插）
			int savedImageX = MemSafeRead<int>((int)rq.plant + 8);
			int savedImageY = MemSafeRead<int>((int)rq.plant + 0xC);
			MemSafeWrite<int>((int)rq.plant + 8, (int)rq.x + 20 - 0x19);
			MemSafeWrite<int>((int)rq.plant + 0xC, (int)rq.y - 110 + 0x2E);
			g_cabbageExtraShooting = true;
			int newProj = fnCabbageShoot((int)rq.plant, bz.GetBaseAddress(), rq.row, 1);
			g_cabbageExtraShooting = false;
			MemSafeWrite<int>((int)rq.plant + 8, savedImageX);
			MemSafeWrite<int>((int)rq.plant + 0xC, savedImageY);
			if (newProj)
			{
				// ★ 轨迹覆写（原生积分：Z(+0x38) 负=离地、vel(+0x44) 负=上升、vel+=0.115/帧、
				//   峰值=vel0²/0.23、落地=下落中 Z 回穿 -30）。整体替换为物理反弹量：
				//   Z=0（起跳平面）、vel=反向缩放值、XSpeed=缩放值 → 纯抛物线飞到哪算哪
				MemSafeWrite<float>(newProj + 0x38, 0.0f);
				MemSafeWrite<float>(newProj + 0x44, nv);
				MemSafeWrite<float>(newProj + 0x3C, nx);
				// 弹射弹本身不再弹射（每发子弹只跳一次；按地址登记，死亡时消费）
				g_cabbageNoBounce[(DWORD)newProj] = 1;
				// ★ 碰撞宽限：出生点就在刚命中的僵尸脚下，第 1 帧碰撞扫描必然与该僵尸
				//   重叠 → 打回同一只。出生即清 [+0x74]（0x531A80 标签检查失败→碰撞全跳过，
				//   西瓜大炮 +0x74 机制的逆向运用），ex>=20 由下方 tick 重新装填原生标签
				int orig74 = MemSafeRead<int>(newProj + 0x74);
				int newId = MemSafeRead<int>(newProj + 0x90);
				MemSafeWrite<int>(newProj + 0x74, 0);
				if (g_cabbageBounceArmCount < 16)
				{
					CabbageBounceArm& ar = g_cabbageBounceArm[g_cabbageBounceArmCount++];
					ar.proj = (DWORD)newProj;
					ar.id = newId;
					ar.orig74 = orig74;
				}
			}
		}
		g_cabbageBounceCount = 0;
	}

	// ===== 弹射弹碰撞重装填 tick：ex>=20 恢复原生 [+0x74] =====
	// 与原版落地检查的 ex>20 宽限期（0x46D598）严格对齐；Id(+0x90) 校验防内存池
	// 复用后误写他人弹体（地址复用只摘槽、绝不能写）
	for (int ai = g_cabbageBounceArmCount - 1; ai >= 0; ai--)
	{
		CabbageBounceArm& ar = g_cabbageBounceArm[ai];
		int curId = MemSafeRead<int>(ar.proj + 0x90);
		if (curId != ar.id)
		{
			g_cabbageBounceArm[ai] = g_cabbageBounceArm[g_cabbageBounceArmCount - 1];
			g_cabbageBounceArmCount--;
			continue;
		}
		BYTE gone = MemSafeRead<BYTE>(ar.proj + 0x50);   // NotExist
		int ex = MemSafeRead<int>(ar.proj + 0x60);       // ExistedTime
		if (!gone && ex >= 20)
			MemSafeWrite<int>(ar.proj + 0x74, ar.orig74);
		if (gone || ex >= 20)
		{
			g_cabbageBounceArm[ai] = g_cabbageBounceArm[g_cabbageBounceArmCount - 1];
			g_cabbageBounceArmCount--;
		}
	}

	// 死亡经验分配移到 onDrawExpUI 处理——绘制 hook 时机更稳定
	// 出怪配置延迟应用（BoardInitAfter 触发时波次数据尚未填充）
	TryApplyWaveConfig(boardAddress);

	// ===== 经验包：延迟加载图片（游戏资源就绪后，与冰锥贴图同理）=====
	// ★ 只尝试一次（成功/失败都不重试）——失败重试会导致每帧泄漏 + 堆耗尽，见 LoadExpPouchImages 注释
	CRASH_STEP("exppouch:images");
	if (!g_expPouchImagesTried)
	{
		g_expPouchImagesTried = true;
		g_expPouchImagesLoaded = true;
		LoadExpPouchImages();
	}

	// ===== 经验文字字形：延迟加载（与经验包同时机，避免绘制期读盘/分配）=====
	// 内部最多尝试 4 次；成功或放弃后 g_expGlyphLoadDone=true，不再重复。
	if (!g_expGlyphLoadDone)
		ExpGlyphLoadOnce();

	// ===== 经验包：延迟安装 hook（游戏代码就绪后，与冰锥/花盆 hook 同理）=====
	if (!g_expPouchDrawHookInstalled)
	{
		g_expPouchDrawHookInstalled = true;
		InstallExpPouchDrawHook();
	}
	if (!g_expPouchHookInstalled)
	{
		g_expPouchHookInstalled = true;
		InstallExpPouchMouseHook();
	}
	// 鼠标坐标 hook（跟随/高亮用）：与其它 hook 同理延迟安装
	if (!g_expPouchMouseMoveHookInstalled)
	{
		g_expPouchMouseMoveHookInstalled = true;
		InstallExpPouchMouseMoveHook();
	}
	// 植物高亮 hook（DrawGameObjects 入口，绘制前设置原生高亮标志）
	if (!g_expPouchHighlightHookInstalled)
	{
		g_expPouchHighlightHookInstalled = true;
		InstallExpPouchHighlightHook();
	}

	// ===== 粒子特效预览器：每帧轮询按键 + 自动轮播 =====
	CRASH_STEP("particlepreview");
	UpdateParticlePreviewer(boardAddress);

	// 本帧 mod 逻辑已全部执行完毕。
	// 若崩溃时 step 停在这里，说明崩溃发生在 **游戏自身后续执行** 中
	// （mod 破坏了游戏状态 → 延迟崩溃），而不是 mod 代码内部。
	CRASH_STEP("onGameObjectsUpdate:return");
}

void onSeedCardClick(DWORD seedcardAddress)
{
}

void onZombieBlast(DWORD zombieAddress)
{
}

void onZombieButter(DWORD zombieAddress)
{
}

void onZombieDecelerate(DWORD zombieAddress)
{
}

void onZombieEat(DWORD zombieAddress, DWORD plantAddress)
{
}

void onZombieFroze(DWORD zombieAddress)
{
}

int onZombieHit(DWORD zombieAddress, PVZ::DamageFlags type, DWORD amount)
{
	return amount;
}

void onZombieHypnotize(DWORD zombieAddress)
{
}

void onZombieRemove(DWORD zombieAddress)
{
	// 剧毒体系：清除该僵尸的毒标记（防僵尸内存池地址复用残留）
	g_poisonStacks.erase(zombieAddress);
	// 寒冰菇冰法阵脆弱标记清理（防僵尸内存池地址复用残留）
	g_iceVulnZombies.erase(zombieAddress);
	// 魅惑菇状态清理：可移动集合与选中状态
	g_hypnoMovableZombies.erase(zombieAddress);
	if (g_hypnoSelectedZombie == zombieAddress)
		g_hypnoSelectedZombie = 0;
	// 玉米投手：清除该僵尸在所有玉米投手下的黄油攻击计数（防内存池地址复用误判）
	for (auto& kv : g_cornPultHits)
		kv.second.erase(zombieAddress);

	// zombie+0x148 由游戏自身维护（所有伤害路径都写入），
	// ZombieInitAfterEvent 已在僵尸创建时清零，无残留风险。
	int plantAddress = MemSafeRead<int>(zombieAddress + 0x148);

	if (plantAddress != 0)
	{
		// 验证植物是否仍然有效
		PVZ::Plant plant(plantAddress);
		if (plant.isValid())
		{
			PVZ::Zombie zombie(zombieAddress);
			// 经验 = 本体 + 一类防具(头盔) + 二类防具(盾牌) 的最大生命值之和
			// ★ 磁力菇：被吸走的铁器不再计入（这份经验已在「消化完成」时发给磁力菇，总量守恒）
			int absorbedHelm   = MagAbsorbedExpHelm(zombieAddress);
			int absorbedShield = MagAbsorbedExpShield(zombieAddress);
			int totalMaxHp = (int)zombie.BodyMaxHealth;
			if (absorbedHelm <= 0)
				totalMaxHp += (int)zombie.HelmMaxHealth;
			// 扶梯僵尸：梯子一旦离身（架到草坪上 / 被磁力菇吸走）就不再计梯子经验
			// 判据：ShieldType 已不是 Ladder 但 ShieldMaxHealth 仍保留（DetachShield 只清 +0xD8/+0xDC）
			bool ladderLeft = ((int)zombie.Type == (int)ZombieType::LadderZombie
				&& (int)zombie.ShieldType != (int)ShieldType::Ladder);
			if (absorbedShield <= 0 && !ladderLeft)
				totalMaxHp += (int)zombie.ShieldMaxHealth;
			if (totalMaxHp < 0) totalMaxHp = 0;

			AddPlantExperience(plantAddress, totalMaxHp);
		}
	}
	// 磁力菇：该僵尸的铁器记录已无意义（死亡结算已用掉）→ 清掉，防记录表膨胀
	MagForgetZombie(zombieAddress);
}

void onZombieInitAfter(DWORD zombieAddress)
{
	// 僵尸创建时清零伤害来源字段，避免内存池复用导致残留旧值
	// （框架 ZombieInitAfterEvent 在本版本不可用——hook 点 0x524035 是函数尾部，
	//   此函数已无人调用，保留仅作防御）
	MemSafeWrite<int>(zombieAddress + 0x148, 0);
}

void onPlantDamageZombie(DWORD infoPtr)
{
	// PlantDamageZombieEvent 回调，覆盖非子弹伤害路径
	// （地刺、倭瓜、食人花、土豆雷等）
	// 注意：樱桃炸弹(CherryBomb)的Effect型爆炸不走此路径！
	// infoPtr 指向 PZDamageInfo：[+0]=zombieAddr, [+4]=plantAddr
	int zombieAddr = MemSafeRead<int>(infoPtr);
	int plantAddr = MemSafeRead<int>(infoPtr + 4);
	if (zombieAddr && plantAddr)
	{
		MemSafeWrite<int>(zombieAddr + 0x148, plantAddr);
	}
}

// ==================== 出怪配置应用 ====================

// ==================== 撑杆司令（PoleCommander）====================
// 自定义僵尸：使用撑杆僵尸(类型3)的贴图和全部机制，但：
//   - 血量 1000（zombie_mechanics.ini 可调）
//   - 有杆时移速 = 普通撑杆僵尸 * SpeedMultiplier（默认 1.5 倍）
//   - 可以跳两次：跳过第 1 个植物后保留杆子继续跑，再跳过第 2 个植物后才丢杆
// 实现要点（全部经反汇编验证，函数表地址有误需以反汇编为准）：
//   - 撑杆僵尸特性更新函数 Zombie::UpdateZombiePolevaulter 实际在 0x524DC0
//     （函数表写 0x525DC0 是错的；类型分派 0x52A110 里 cmp [esi+0x24],3 → call 0x524DC0）
//     - 状态 0xB(POLE_VALUTING_RUNNING 持杆跑)：到植物前起跳 → 状态 0xC 播放 anim_jump
//       （起跳时清 [zombie+0xBC] 杆子标志、把跳跃水平速度写入 [zombie+0x34]）
//     - 状态 0xC 动画播完落地 → 状态 0xD(POLE_VAULTING_WALKING 无杆走路) 丢杆
//   - 本 DLL 在 0x524DC0 入口装 trampoline，每帧回调：
//       a) 首次见到某只类型3僵尸 → 按"本波第几个类型3槽位"匹配 waves.ini 的
//          PoleCommander 槽位 → 标记为司令（写血量，记录基础移速）
//       b) 司令每帧：状态0xB 时强制移速 = 基础移速 * 倍率（游戏不每帧改写+0x34）
//       c) 司令落地（状态 0xC→0xD 跳变）且跳跃次数<2 → 重新上杆：
//          状态=0xB、[0xBC]=1(有杆)、[0x64]=0(高度)、[0x7C]=-1(清目标列)、移速恢复
//   - 槽位计数按"波内类型3僵尸数量"推进，随 CurrentWave(0x557C) 变化而重置；
//     蹦极空投/僵王召唤出的类型3僵尸会干扰计数（已知边界，属可接受范围）
// 全局变量声明在文件顶部"撑杆司令（PoleCommander）全局状态"处。

// 加载 zombie_mechanics.ini（[PoleCommander] / [BlastproofDoorZombie] 节）
void LoadZombieMechanicsConfig()
{
	g_polevaulterSpeedMult = 1.5f;
	g_polevaulterHp = 1000;
	g_blastDoorHp = 1100;
	g_blastBucketHp = 1100;
	g_blastBodyHp = 200;
	g_blastMaxDamage = 200;

	std::ifstream file("zombie_mechanics.ini");
	if (!file.is_open())
		return;

	std::string line;
	std::string section; // 当前节名（空=未在任何节内）
	while (std::getline(file, line))
	{
		std::string trimmed = TrimString(line);
		if (trimmed.empty() || trimmed[0] == ';' || trimmed[0] == '#')
			continue;

		// 节名
		if (trimmed[0] == '[' && trimmed.back() == ']')
		{
			section = TrimString(trimmed.substr(1, trimmed.size() - 2));
			continue;
		}
		if (section.empty())
			continue;

		size_t eqPos = trimmed.find('=');
		if (eqPos == std::string::npos)
			continue;
		std::string key = TrimString(trimmed.substr(0, eqPos));
		std::string value = TrimString(trimmed.substr(eqPos + 1));
		if (value.empty())
			continue;

		try
		{
			if (section == "PoleCommander")
			{
				if (key == "SpeedMultiplier")
					g_polevaulterSpeedMult = SafeAtof(value.c_str());
				else if (key == "Hp")
					g_polevaulterHp = SafeAtoi(value.c_str());
			}
			else if (section == "BlastproofDoorZombie")
			{
				if (key == "DoorHp")
					g_blastDoorHp = SafeAtoi(value.c_str());
				else if (key == "BucketHp")
					g_blastBucketHp = SafeAtoi(value.c_str());
				else if (key == "BodyHp")
					g_blastBodyHp = SafeAtoi(value.c_str());
				else if (key == "MaxDamagePerHit")
					g_blastMaxDamage = SafeAtoi(value.c_str());
			}
		}
		catch (...) {}
	}
	file.close();
}

// 标记一只类型3僵尸是否为撑杆司令（在 UpdatePoleCommanderFrame 每帧轮询里调用）
static void MarkPoleCommander(DWORD zombieAddr)
{
	if (!zombieAddr)
		return;
	int type = MemSafeRead<int>(zombieAddr + 0x24);
	if (type != (int)ZombieType::PoleVaultingZombie)
		return;
	// 用僵尸唯一 Id(+0x158) 做键：DataArray 槽位地址会被回收复用，地址不能当身份
	int zid = MemSafeRead<int>(zombieAddr + 0x158);
	if (g_seenPoleVaulters.find(zid) != g_seenPoleVaulters.end())
		return;
	g_seenPoleVaulters.insert(zid);

	// 类型3序号计数（与 TryApplyWaveConfig 转写侧的 type3Idx 语义一致）
	int slot3 = g_type3SeenInWave;
	g_type3SeenInWave++;

	int boardAddr = MemSafeRead<int>(PVZ_BASE + 0x768);
	if (!boardAddr)
		return;
	// ★ CurrentWave(0x557C) 是 1-based（1=第一波，实测 [mark] 日志：第4波读到 4）！
	//   进度条函数 0x4132FC 用 ebp-1 也佐证。必须 -1 转 0-based 与 g_commanderWaveSlots
	//   （TryApplyWaveConfig 用波次索引 0~N-1 记录）对齐，否则永远错位 1 匹配不上。
	int wave = MemSafeRead<int>(boardAddr + 0x557C) - 1;
	if (wave < 0)
		wave = 0; // 波次开始前 CurrentWave=0 → 归 0（Wave0 一般无司令配置，查不到即 normal）
	auto it = g_commanderWaveSlots.find(wave);
	bool isCommander = (it != g_commanderWaveSlots.end() && it->second.count(slot3) != 0);

	if (!isCommander)
		return;

	g_commanderZombies.insert(zid);
	// 捕获游戏原生持杆跑速（创建时已写入 +0x34；越界则回退 2.5）
	float base = MemSafeRead<float>(zombieAddr + 0x34);
	if (base < 0.5f || base > 6.0f)
		base = 2.5f;
	g_cmdrBaseSpeed[zid] = base;
	g_cmdrJumps[zid] = 0;
	g_cmdrLastState[zid] = MemSafeRead<int>(zombieAddr + 0x28); // 落地检测基线
	g_cmdrPrevX[zid] = MemSafeRead<float>(zombieAddr + 0x2C);   // 测量法基准
	// 血量（本体生命/上限）
	MemSafeWrite<int>(zombieAddr + 0xC8, g_polevaulterHp);
	MemSafeWrite<int>(zombieAddr + 0xCC, g_polevaulterHp);
	// 有杆跑速 1.5 倍（游戏跑步期间不改写 +0x34；起跳会覆盖为跳速，落地后轮询恢复）
	MemSafeWrite<float>(zombieAddr + 0x34, base * g_polevaulterSpeedMult);
}

// 加载司令皮肤贴图（4 张司令版 + 2 张原版对比，寒冰射手同款加载法）
// 原版 upper/upper2 指针用于"关键帧扫描替换"（upper2 无独立轨道，是 upper 轨道的第二帧贴图）
// __try 放独立函数：本函数只含内置类型 + FILE*（无 C++ 对象展开，避开 C2712）
static void LoadCommanderSkinImages()
{
	__try
	{
		// 司令版贴图（槽位 0=hair 1=body1 2=upper 3=upper2）：文件名（反斜杠 + 正斜杠备选）+ 日志名
		static const char* kFiles[4] = {
			"reanim\\Zombie_polecommander_hair.png",
			"reanim\\Zombie_polecommander_body1.png",
			"reanim\\Zombie_polecommander_outerarm_upper.png",
			"reanim\\Zombie_polecommander_outerarm_upper2.png",
		};
		static const char* kFilesFwd[4] = {
			"reanim/Zombie_polecommander_hair.png",
			"reanim/Zombie_polecommander_body1.png",
			"reanim/Zombie_polecommander_outerarm_upper.png",
			"reanim/Zombie_polecommander_outerarm_upper2.png",
		};
		for (int i = 0; i < 4; i++)
		{
			if (g_cmdrSkinImages[i] != 0)
				continue;
			Draw::PString filename = Draw::ToString(kFiles[i]);
			Draw::PString variant = Draw::ToString("");
			DWORD isNew = 0;
			DWORD sharedImg = Draw::GetSharedImage(isNew, variant, filename);
			if (sharedImg == 0)
			{
				Draw::PString filename2 = Draw::ToString(kFilesFwd[i]);
				sharedImg = Draw::GetSharedImage(isNew, variant, filename2);
			}
			if (sharedImg != 0)
			{
				g_cmdrSkinImages[i] = Draw::SharedImageRefToImage(sharedImg);
			}
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		// 资源系统未就绪等异常：保持未加载，下帧重试
		g_cmdrSkinImageLoaded = false;
	}
}

// 实际执行换皮肤（无 __try，可含局部对象；被 ApplyCommanderSkin 的 __try 包裹）
// 框架封装：Animation::FindTrackIndex(0x472F30) + Animation::SetImageOverride(0x473490)，
// 运行时地址均经框架作者验证（0x47 区域文件字节不可信，勿反汇编验证）。
// hair/body1 轨道名均已实测（idx=24/21），SetImageOverride 直达。
// ★upper（含 upper2）：upper2 没有独立轨道——FindTrackIndex("..._upper2") 返回 0 是"找不到"的
//   误匹配（rdata 只有 IMAGE_..._OUTERARM_UPPER2 图像枚举、无独立轨道名字符串）；upper2 是
//   "掉手之后"（无杆走路 state=0xD）时 upper 轨道显示的第二张关键帧贴图。SetImageOverride 是
//   轨道级单覆写管不到关键帧切换 → 按状态切换 override 贴图（掉手后整个轨道显示 commander_upper2，
//   持杆/跳跃显示 commander_upper）。★指针扫描方案实测无效（轨道实例无原版贴图指针，勿再试）。
static bool ApplyCommanderSkinInner(DWORD zombieAddr)
{
	if (!zombieAddr)
		return false;
	// 防御：类型必须还是撑杆僵尸（地址可能被池回收复用）
	int type = MemSafeRead<int>(zombieAddr + 0x24);
	if (type != (int)ZombieType::PoleVaultingZombie)
		return false;

	PVZ::Animation anim(0);
	int animBase = TryGetZombieReanim(zombieAddr, anim) ? anim.GetBaseAddress() : 0;
	if (!animBase)
		return false;
	// 判定放宽：用 upper 轨道命中代替 anim_walk——跳跃(anim=0x7)/无杆走路动画实例可能没有
	// anim_walk 轨道，会导致掉手后整个函数提前 return（v2 实测 kfUpper=0 且掉手后仍原版的根因）；
	// upper 轨道在所有撑杆动画实例里都存在（手臂始终要画）。同时防 +0x118=0 误匹配无关动画。
	if (anim.FindTrackIndex("Zombie_polevaulter_outerarm_upper") < 0)
		return false;

	// 当前状态：13(0xD)=无杆走路（掉手后）。跳跃/持杆跑用 upper 贴图，无杆走路用 upper2 贴图。
	// ★只按 state==0xD 判断（不用 jumps>=2）：跳满 2 次只是"第二次跳跃完成"，游戏可能还没切到
	//   无杆走路动画（掉手画面），jumps>=2 会过早换成 upper2（实测：跳过两次就变 upper2）。
	int state = MemSafeRead<int>(zombieAddr + 0x28);
	bool noPole = (state == 0xD);

	// hair / body1 / upper：★ 2026-10-16 全部改走 ReanimSetImageOverride。
	//   ★ 这是"选卡/进游戏不定期崩溃"的高危来源之一：上面只证明了 upper 轨道在**该动画实例**里存在；
	//     而僵尸的当前动画实例是按动作分别建的对象（持杆跑 / 跳跃 / 无杆走路 …），轨道表并不相同 ——
	//     跳跃或无杆走路实例很可能没有 anim_hair / Zombie_polevaulter_body1。
	//     注意：0x472F30 找不到名字时**返回 0**，所以"写错轨道"不是崩因；
	//     但 anim 指针一旦是垃圾（框架 INVALID_BASEADDRESS=0x400000 等）就会变成任意地址写。
	//     ReanimSetImageOverride 会先把 reanim 卡成"可写堆对象 + 名字真命中"，两者都过才动手。
	{
		if (g_cmdrSkinImages[0])
			ReanimSetImageOverride(animBase, "anim_hair", g_cmdrSkinImages[0]);
		if (g_cmdrSkinImages[1])
			ReanimSetImageOverride(animBase, "Zombie_polevaulter_body1", g_cmdrSkinImages[1]);
	}
	// upper：按状态切换贴图（★掉手后=upper2 司令版，持杆/跳跃=upper 司令版）
	//   ——upper2 无独立轨道（FindTrackIndex 返回 0 是"找不到"误匹配），它是 upper 轨道在
	//   无杆走路时的第二张关键帧贴图；SetImageOverride 轨道级单覆写管不到关键帧切换，
	//   所以直接按状态换 override 贴图（无杆走路时整个轨道显示 commander_upper2）。
	DWORD upperImg = noPole ? g_cmdrSkinImages[3] : g_cmdrSkinImages[2];
	if (upperImg)
		ReanimSetImageOverride(animBase, "Zombie_polevaulter_outerarm_upper", upperImg);

	return true;
}

// 给司令换 4 处皮肤贴图（幂等，可每帧调用；动画实例切换后自动重新生效）
// 返回 true=已执行 / false=暂不可用（动画未就绪等，下帧重试，静默）
static bool ApplyCommanderSkin(DWORD zombieAddr)
{
	__try
	{
		return ApplyCommanderSkinInner(zombieAddr);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		return false;
	}
}

// 司令每帧逻辑（轮询版）
// ★实测修正（日志 [poll] 铁证）：
//   1) state 十进制 11=持杆跑 / 12=跳跃 / 13=无杆走路（与 0xB/0xC/0xD 数值恰同）
//   2) +0x34 不是速度字段（跳跃/走路时值仅 -0.2~0.34，游戏移动用查表）——写它无效，
//      移速必须用测量法；且僵尸向左 X 递减 moved 为负，判断要用绝对值
//   3) +0x64/+0x7C/+0xBC 均不是高度/目标列/杆标志（日志恒 0/-1）——写它们无害但无效
//   4) "只在落地帧写一次 state=0xB"不够：游戏 state 13（无杆走）分支会覆盖并切无杆动画
//   5) ★最终方案：起跳计数 + 持续强制持杆跑——jumps<2 且非跳跃中每帧写回 state=0xB，
//      让游戏一直执行 state 11 分支（持杆动画+查表持杆速度+起跳判定），
//      自然获得 1.5 倍速（测量法）与二段跳；跳满 2 次后放行原版丢杆
static void UpdateCommanderFrame(DWORD zombieAddr, int zid)
{
	int state = MemSafeRead<int>(zombieAddr + 0x28);
	int prev = g_cmdrLastState[zid];

	// 起跳检测（跳跃开始）：state 变 12 即一次跳跃（含第一次自然起跳和第二次强制后起跳）
	if (state == 0xC && prev != 0xC)
	{
		int jumps = g_cmdrJumps[zid] + 1;
		g_cmdrJumps[zid] = jumps;
	}

	// 持杆跑稳定期快照动画实例（延迟 15 帧确保动画初始化完成；快照=含杆子的完整状态）
	if (state == 0xB && g_cmdrJumps[zid] == 0)
	{
		int rf = g_cmdrRunFrames[zid] + 1;
		g_cmdrRunFrames[zid] = rf;
		if (rf >= 15 && g_cmdrAnimSnapTaken.count(zid) == 0)
		{
			g_cmdrAnimSnapTaken.insert(zid);
			PVZ::Animation anim(0);
			int animBase = TryGetZombieReanim(zombieAddr, anim) ? anim.GetBaseAddress() : 0;
			if (animBase)
			{
				std::array<BYTE, 0xA0>& snap = g_cmdrAnimSnap[zid];
				PVZ::Memory::ReadArray<BYTE>(animBase, snap.data(), 0xA0);
			}
		}
	}
	else if (state != 0xB)
	{
		g_cmdrRunFrames[zid] = 0; // 离开持杆跑清零（跳跃/无杆时）
	}

	// 跳了 <2 次且非跳跃中：持续强制持杆跑（让游戏一直走 state 11 分支）
	if (g_cmdrJumps[zid] < 2 && state != 0xC)
	{
		if (state != 0xB)
		{
			// 落地/无杆走帧：强制回到持杆跑（游戏下帧按 state 11 分支处理：持杆动画+起跳判定）
			MemSafeWrite<int>(zombieAddr + 0x28, 0xB); // 持杆跑
			MemSafeWrite<int>(zombieAddr + 0x64, 0);   // 复位（原"高度"猜测，写0无害）
			MemSafeWrite<int>(zombieAddr + 0x7C, -1);  // 复位（原"目标列"猜测）
			MemSafeWrite<BYTE>(zombieAddr + 0xBC, 1);  // ★杆子标志=1
			// ★★动画实例整块写回（终极方案）：tdiff 证实杆子显示状态在动画实例内部
			//   （游戏丢杆=重写动画实例内容——pole 轨道从"未播放"变"播放中"），单字段/轨道
			//   渲染组/SetAnimation 都救不回。持杆跑稳定期已快照整个动画实例 0xA0 字节，
			//   force 时整块写回 = 恢复持杆走路完整状态（含杆子+上举手臂轨道）
			//   写回时保留当前 transform（0x24~0x3B：XScale/XSlant/XOffset/YScale/YSlant/YOffset）：
			//     快照（持杆跑）与落地时动画实例偏移不同，整块写回会把偏移还原 → 视觉瞬移
			{
				auto itSnap = g_cmdrAnimSnap.find(zid);
				if (itSnap != g_cmdrAnimSnap.end())
				{
					PVZ::Animation anim(0);
					int animBase = TryGetZombieReanim(zombieAddr, anim) ? anim.GetBaseAddress() : 0;
					if (animBase)
					{
						BYTE curXf[0x18];
						PVZ::Memory::ReadArray<BYTE>(animBase + 0x24, curXf, 0x18);
						PVZ::Memory::WriteArray<BYTE>(animBase, itSnap->second.data(), 0xA0);
						PVZ::Memory::WriteArray<BYTE>(animBase + 0x24, curXf, 0x18);
					}
				}
			}
			state = 0xB;
			// ★落地帧重置补速基准（跳过本帧补速）——否则 moved=当前X-跳跃中prevX 可能吞下
			//   跳跃最后一段位移，补速推出半个跳跃距离 = "落地瞬移"（实测约 83px ≈ 跳跃一半）
			g_cmdrPrevX[zid] = MemSafeRead<float>(zombieAddr + 0x2C);
		}
		else
		{
			// 稳定持杆跑帧：移速测量法补速（僵尸向左 X 递减 moved 为负 → 用绝对值判断）
			float x = MemSafeRead<float>(zombieAddr + 0x2C);
			auto it = g_cmdrPrevX.find(zid);
			if (it != g_cmdrPrevX.end())
			{
				float moved = x - it->second;
				float am = moved < 0 ? -moved : moved;
				if (am > 0.05f)
					MemSafeWrite<float>(zombieAddr + 0x2C, x + moved * 0.5f); // 补50%
			}
		}

		// ★★杆子标志：+0xBC（1=持杆 0=丢杆，字段快照 diff 铁证 +BC:00000001>00000000）！
		//   游戏无杆走路逻辑会清 +0xBC，必须每帧写回 1（回调在游戏 Update 之后运行，能压住）
		MemSafeWrite<BYTE>(zombieAddr + 0xBC, 1);
	}

	// ★prevX 无条件每帧更新（函数末尾，任何 state 都执行）：
	//   跳跃中也要跟随（否则跳跃期间 prevX 停在跳跃前 → 落地后 moved=整个跳跃位移 → 瞬移！）
	//   记录"补后"值 → 下帧 moved 只含游戏移动 → 补速精确 50%
	g_cmdrPrevX[zid] = MemSafeRead<float>(zombieAddr + 0x2C);

	// 跳满 2 次：放行原版丢杆逻辑（不干预），恢复正常无杆行为
	g_cmdrLastState[zid] = state;
}

// __try 独立包装（UpdateCommanderFrame 无局部对象，可直接包；防僵尸地址被回收等异常）
static void SafeUpdateCommander(DWORD zaddr, int zid)
{
	__try
	{
		UpdateCommanderFrame(zaddr, zid);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 撑杆司令每帧轮询入口（onGameObjectsUpdate 调用；零 hook，纯内存遍历）
// ★ 本函数含 std::vector 局部对象（GetAllZombies），__try 只能放独立函数里（C2712）
static void UpdatePoleCommanderFrame(DWORD boardAddress)
{
	if (!boardAddress)
		return;
	PVZ::Board board(boardAddress);
	if (!board.GetBaseAddress())
		return;
	auto zombies = board.GetAllZombies();

	// 1. 标记新出现的类型3僵尸（MarkPoleCommander 内部去重 + 按"本波第几个类型3"匹配司令槽位）
	for (auto& z : zombies)
	{
		if (z.NotExist)
			continue;
		int zaddr = z.GetBaseAddress();
		if (!zaddr)
			continue;
		int type = MemSafeRead<int>(zaddr + 0x24);
		if (type != (int)ZombieType::PoleVaultingZombie)
			continue;
		MarkPoleCommander(zaddr);
	}

	// 2. 已标记司令的每帧逻辑（移速 + 二段跳落地检测）
	for (auto& z : zombies)
	{
		if (z.NotExist)
			continue;
		int zaddr = z.GetBaseAddress();
		if (!zaddr)
			continue;
		int zid = MemSafeRead<int>(zaddr + 0x158);
		if (g_commanderZombies.count(zid) == 0)
			continue;
		SafeUpdateCommander(zaddr, zid);
	}
}

// 每帧检测波次变化，重置类型3/类型6槽位计数（须在轮询标记之前调用）
static void UpdatePoleVaulterWaveTracking(DWORD boardAddress)
{
	if (!boardAddress)
		return;
	int wave = MemSafeRead<int>(boardAddress + 0x557C); // CurrentWave
	if (wave != g_lastSeenWave)
	{
		g_lastSeenWave = wave;
		g_type3SeenInWave = 0;
		g_type6SeenInWave = 0; // 防爆门僵尸复用同一波次检测（类型6计数）
	}
}

// ==================== 防爆门僵尸（BlastproofDoorZombie）====================
// 自定义僵尸：铁门僵尸(类型6) + 铁桶(头盔) 双防具，出场由 waves.ini 的
// BlastproofDoorZombie 控制（槽位按铁门僵尸出怪，见 TryApplyWaveConfig）。
// 机制：
//   - 铁门（盾牌 +0xDC）+ 铁桶（头盔 +0xD0）双防具，血量来自 zombie_mechanics.ini
//     [BlastproofDoorZombie] 节（仅对本僵尸生效，普通铁桶/铁门僵尸数值不受影响）
//   - 铁门存在时（ShieldHealth > 0），受到的任何伤害限伤 MaxDamagePerHit（默认 200）：
//     子弹/窝瓜/土豆雷/灰烬等全部走 Zombie::TakeDamage(0x5317C0)，
//     无视防具的本体伤害走 Zombie::TakeBodyDamage(0x5312D0)，两个入口都限流。
//     小推车（LawnMower::MowZombie@0x458540）直接击杀不走伤害结算 → 天然无视限伤 ✅
//   - 铁门被打破后（ShieldHealth=0）限伤解除，本体正常结算
// 实现要点（同撑杆司令）：0x52/0x53 僵尸区域运行时可能解密，事件 hook 不可用 →
//   onGameObjectsUpdate 每帧纯内存轮询标记（零 hook）；限伤 hook 安装前逐字节探测
//   运行时序言（与文件字节一致才装，防截断指令崩溃）。

// 铁桶贴图：显示僵尸 reanim 的 "anim_bucket" 轨道（与 EquipBucket 同款做法）。
// 共享 Zombie.reanim 内含全部僵尸轨道（anim_bucket/anim_screendoor 等都在），
// 铁门僵尸默认隐藏铁桶轨道，AssignRenderGroupToPrefix(0,...) 打开即可。
// 每帧重设（幂等）：铁桶生命 >0 时持续显示；铁桶破裂后停止 → 游戏隐藏逻辑生效。
// ★C2712：__try 放外层包装，局部对象（PVZ::Zombie/Animation）放内层函数
static void ApplyBlastBucketVisualInner(DWORD zombieAddr)
{
	if (!zombieAddr)
		return;
	int helmHp = MemSafeRead<int>(zombieAddr + 0xD0); // 铁桶生命
	if (helmHp <= 0)
		return; // 铁桶已破：放行游戏隐藏铁桶轨道
	PVZ::Animation anim(0);
	if (!TryGetZombieReanim(zombieAddr, anim))
		return;
	anim.AssignRenderGroupToPrefix(0, "anim_bucket"); // 显示铁桶轨道（无匹配轨道时是空操作）
}

static void ApplyBlastBucketVisual(DWORD zombieAddr)
{
	__try
	{
		ApplyBlastBucketVisualInner(zombieAddr);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ============ 铁门贴图替换（防爆门专用 Blastproof_screendoor1/2/3）============
// 原版铁门轨道 anim_screendoor 显示 Zombie_screendoor1/2/3.png，破损等级由盾牌伤害
// 处理器 0x530BC0 按 ShieldHealth 比例切换（等级0=完好 hp>=2Max/3、等级1 hp>=Max/3、
// 等级2 hp<Max/3，反汇编 0x530C55-0x530C90 铁证）。本模块对"已标记的防爆门"每帧
// SetImageOverride("anim_screendoor", Blastproof{level+1}) 幂等覆盖——原版等级2 自身
// 就用 SetImageOverride(0x473490) 显示三级破损，证明该轨道 override 有效；
// 等级1 原版写轨道内存（关键帧数据），我们的显示层 override 优先级更高，每帧重设盖住。
// 普通铁门僵尸不在此集合 → 完全不受影响。

// 加载 3 张替换贴图（懒加载；资源系统未就绪时保持 0，下帧重试）。
// ★C2712：__try 内只用内置类型（同 LoadCommanderSkinImages 模式）
static void LoadBlastDoorImages()
{
	__try
	{
		if (g_blastDoorImageLoaded)
			return;
		static const char* kFiles[3] = {
			"reanim\\Blastproof_screendoor1.png",
			"reanim\\Blastproof_screendoor2.png",
			"reanim\\Blastproof_screendoor3.png",
		};
		static const char* kFilesFwd[3] = {
			"reanim/Blastproof_screendoor1.png",
			"reanim/Blastproof_screendoor2.png",
			"reanim/Blastproof_screendoor3.png",
		};
		bool allLoaded = true;
		for (int i = 0; i < 3; i++)
		{
			if (g_blastDoorImages[i] != 0)
				continue;
			Draw::PString filename = Draw::ToString(kFiles[i]);
			Draw::PString variant = Draw::ToString("");
			DWORD isNew = 0;
			DWORD sharedImg = Draw::GetSharedImage(isNew, variant, filename);
			if (sharedImg == 0)
			{
				Draw::PString filename2 = Draw::ToString(kFilesFwd[i]);
				sharedImg = Draw::GetSharedImage(isNew, variant, filename2);
			}
			if (sharedImg != 0)
				g_blastDoorImages[i] = Draw::SharedImageRefToImage(sharedImg);
			else
				allLoaded = false;
		}
		if (allLoaded)
			g_blastDoorImageLoaded = true;
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		// 资源系统未就绪等异常：保持未加载，下帧重试
	}
}

// 实际执行换贴图（无 __try，可含局部对象；被 ApplyBlastDoorTexture 的 __try 包裹）
static void ApplyBlastDoorTextureInner(DWORD zombieAddr)
{
	if (!zombieAddr)
		return;
	if (!g_blastDoorImageLoaded)
		return; // 贴图未就绪（下帧重试）
	int shieldHp = MemSafeRead<int>(zombieAddr + 0xDC);   // 铁门（盾牌）生命
	if (shieldHp <= 0)
		return; // 铁门已破：放行游戏隐藏铁门轨道（0x530A00 破门处理）
	int shieldMax = MemSafeRead<int>(zombieAddr + 0xE0); // 铁门上限
	if (shieldMax <= 0)
		return;
	// 破损等级（与原版 0x530BC0 阈值一致：1/3 与 2/3；整数乘法防溢出，血量最大 1100）
	int level = 0;
	if (shieldHp * 3 < shieldMax)          // hp < max/3 → 二级破损
		level = 2;
	else if (shieldHp * 3 < shieldMax * 2) // max/3 <= hp < 2max/3 → 一级破损
		level = 1;
	if (g_blastDoorImages[level] == 0)
		return;
	PVZ::Animation anim(0);
	int animBase = TryGetZombieReanim(zombieAddr, anim) ? anim.GetBaseAddress() : 0;
	if (!animBase)
		return;
	// 每帧幂等重设：覆盖 anim_screendoor 轨道的任何显示（含原版等级切换写内存）
	// ★★ 2026-10-16 修：这里原来直接 anim.SetImageOverride("anim_screendoor", ...)。
	//    僵尸"当前动画实例"是按动作分别建的对象（走路/啃咬/死亡/掉头…），轨道表并不相同；
	//    改走 ReanimSetImageOverride —— 它会先在纯内存里确认 reanim 是**可写堆对象**、
	//    且 anim_screendoor 真在该实例的表里命中，才允许调用游戏函数 0x473490
	//    （该函数在 reanim 为垃圾指针时会用垃圾 count 算出任意下标 → 任意地址写 → 堆损坏）。
	//    顺带也不再走框架 Memory::Execute 的"每次调用 new/delete 一个堆块"。
	ReanimSetImageOverride(animBase, "anim_screendoor", g_blastDoorImages[level]);
}

static void ApplyBlastDoorTexture(DWORD zombieAddr)
{
	__try
	{
		ApplyBlastDoorTextureInner(zombieAddr);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// 标记一只类型6僵尸是否为防爆门（在 UpdateBlastproofDoorFrame 每帧轮询里调用）
static void MarkBlastproofDoor(DWORD zombieAddr)
{
	if (!zombieAddr)
		return;
	int type = MemSafeRead<int>(zombieAddr + 0x24);
	if (type != (int)ZombieType::ScreenDoorZombie)
		return;
	// 用僵尸唯一 Id(+0x158) 做键：DataArray 槽位地址会被回收复用，地址不能当身份
	int zid = MemSafeRead<int>(zombieAddr + 0x158);
	if (g_seenType6.find(zid) != g_seenType6.end())
		return;
	g_seenType6.insert(zid);

	// 类型6序号计数（与 TryApplyWaveConfig 转写侧的 type6Idx 语义一致）
	int slot6 = g_type6SeenInWave;
	g_type6SeenInWave++;

	int boardAddr = MemSafeRead<int>(PVZ_BASE + 0x768);
	if (!boardAddr)
		return;
	// ★ CurrentWave(0x557C) 是 1-based（1=第一波），必须 -1 转 0-based 与
	//   g_blastWaveSlots（TryApplyWaveConfig 用波次索引 0~N-1 记录）对齐
	int wave = MemSafeRead<int>(boardAddr + 0x557C) - 1;
	if (wave < 0)
		wave = 0;
	auto it = g_blastWaveSlots.find(wave);
	bool isBlast = (it != g_blastWaveSlots.end() && it->second.count(slot6) != 0);

	if (!isBlast)
		return;

	g_blastDoorZombies.insert(zid);
	// 双防具 + 本体血量（zombie_mechanics.ini 可调，仅对本僵尸生效）
	// 铁门（盾牌）：类型6由游戏构造函数已设为 ShieldType=ScreenDoor + AttachShield，
	//   这里只覆盖配置血量
	MemSafeWrite<int>(zombieAddr + 0xDC, g_blastDoorHp);  // ShieldHealth
	MemSafeWrite<int>(zombieAddr + 0xE0, g_blastDoorHp);  // ShieldMaxHealth
	// 铁桶（头盔）
	MemSafeWrite<int>(zombieAddr + 0xC4, (int)HelmType::Bucket); // HelmType
	MemSafeWrite<int>(zombieAddr + 0xD0, g_blastBucketHp); // HelmHealth
	MemSafeWrite<int>(zombieAddr + 0xD4, g_blastBucketHp); // HelmMaxHealth
	// 本体
	MemSafeWrite<int>(zombieAddr + 0xC8, g_blastBodyHp);   // BodyHealth
	MemSafeWrite<int>(zombieAddr + 0xCC, g_blastBodyHp);   // BodyMaxHealth
	// 铁桶贴图（显示 anim_bucket 轨道；动画未就绪时静默，后续每帧重试）
	ApplyBlastBucketVisual(zombieAddr);
}

// 防爆门僵尸每帧轮询入口（onGameObjectsUpdate 调用；零 hook，纯内存遍历）
// ★ 本函数含 std::vector 局部对象（GetAllZombies），__try 只能放独立函数里（C2712）
static void UpdateBlastproofDoorFrame(DWORD boardAddress)
{
	if (!boardAddress)
		return;
	PVZ::Board board(boardAddress);
	if (!board.GetBaseAddress())
		return;
	auto zombies = board.GetAllZombies();

	// 铁门替换贴图懒加载（首次成功置标志）
	// ★ 2026-10-16：原来失败是"每帧重试"，而每次 Draw::ToString/GetSharedImage 都会漏
	//   一块 ≥1KB 的堆内存（框架 AllocMemory 最小 1 页且调用方不回收）→ 堆耗尽 → bad_alloc/随机 AV。
	//   现在统一限流（最多 600 次），失败就永久放弃。
	if (!g_blastDoorImageLoaded && ImageLoadRetryAllowed(4))
		LoadBlastDoorImages();

	// 1. 标记新出现的类型6僵尸（MarkBlastproofDoor 内部去重 + 按"本波第几个类型6"匹配）
	// 2. 已标记防爆门的每帧：重设铁桶贴图 + 铁门替换贴图（动画实例切换后自动重新生效）
	for (auto& z : zombies)
	{
		if (z.NotExist)
			continue;
		int zaddr = z.GetBaseAddress();
		if (!zaddr)
			continue;
		int type = MemSafeRead<int>(zaddr + 0x24);
		if (type != (int)ZombieType::ScreenDoorZombie)
			continue;
		MarkBlastproofDoor(zaddr);
		int zid = MemSafeRead<int>(zaddr + 0x158);
		if (g_blastDoorZombies.count(zid) != 0)
		{
			ApplyBlastBucketVisual(zaddr);
			ApplyBlastDoorTexture(zaddr);
		}
	}
}

// ==================== 防爆门僵尸：伤害限流 hook ====================
// 铁门存在时（ShieldHealth>0）任何伤害限 MaxDamagePerHit（默认200）。
// 覆盖三个伤害/击杀入口（反汇编 0x41D8A0 灰烬爆炸函数确认全路径）：
//   0x5317C0 Zombie::TakeDamage(theDamageFlags=eax, theDamage=[esp+4], this=esi)
//             —— 子弹/窝瓜碾压/土豆雷/灰烬等全部伤害结算入口（灰烬用 1800+0x12 标志）
//   0x5312D0 Zombie::TakeBodyDamage(theDamageFlags, theDamage=[esp+8], this=[esp+4])
//             —— 无视防具的本体伤害（仅被 TakeDamage 内部调用，防御性覆盖）
//   0x532B70 Zombie::ApplyBurn —— ★灰烬直接化灰入口（樱桃/毁灭/倭瓜等灰烬植物的
//             "化灰模式"分支不走任何伤害结算，防爆门会被一击化灰！需单独拦截，
//             见 InstallBlastBurnHook）
// 小推车 MowZombie@0x458540 直接击杀不走这三个入口 → 天然无视限伤 ✅
//
// trampoline（入口 pushad 压 32 字节后）：
//   TakeDamage:     [esp+0x24]=伤害, esi=僵尸
//   TakeBodyDamage: [esp+0x24]=僵尸, [esp+0x28]=伤害
//   统一：eax=僵尸, ecx=伤害 → push ecx; push eax; call CapBlastDoorDamage;
//         add esp,8; mov [esp+伤害槽], eax（写回限伤值）; popad; 原7字节; jmp 回
//
// ★★★ 安全设计：0x52/0x53 僵尸区域运行时可能解密（0x52xxxx 已有铁证），hook 前必须
//   逐字节核对运行时前 7 字节与文件序言一致，不一致则跳过该 hook（防截断指令崩溃）。
//   TakeDamage 入口被游戏高频调用，任何错误 hook 都会立刻崩溃，保守探测是唯一安全方案。

// 限伤核心（trampoline 直接 rel32 call，__cdecl；参数：zombieAddr, damage）
static int __cdecl CapBlastDoorDamage(DWORD zombieAddr, int damage)
{
	__try
	{
		if (damage <= g_blastMaxDamage)
			return damage; // 快速路径：不超过上限直接放行（多数子弹伤害）
		if (!zombieAddr)
			return damage;
		int zid = MemSafeRead<int>(zombieAddr + 0x158);
		if (g_blastDoorZombies.count(zid) == 0)
			return damage; // 非防爆门僵尸正常结算
		// 铁门（盾牌）生命 > 0 才限伤；铁门已破 → 解除限伤
		if (MemSafeRead<int>(zombieAddr + 0xDC) <= 0)
			return damage;
		return g_blastMaxDamage;
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		return damage; // 任何异常一律放行（保底不破坏游戏）
	}
}

// 毁灭菇领域穿甲：对僵尸调用原版 TakeBodyDamage（pvzclass z.HitBody 同封装路径，
// 只伤本体、无视一类/二类防具；死亡结算/经验归因均由原版伤害流程处理）。
// 已有先例：onPlantRemove 樱桃等阶爆炸同封装调用，事件/hook 上下文安全。
static void DoomDomainPierce(DWORD zombieAddr, int damage)
{
	__try
	{
		PVZ::Zombie zombie(zombieAddr);
		if (!zombie.isValid() || zombie.NotExist) return;
		zombie.HitBody(damage);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_doomFxErr++;
	}
}

// 寒冰菇 3阶冰法阵脆弱增伤 + 毁灭菇领域穿甲 + 防爆门限伤 合并入口（仅挂在 TakeDamage 外层）
// ★ 只在 TakeDamage(0x5317C0) 这一路生效（i==0），TakeBodyDamage 内部那一路继续走纯限伤，
//   避免"TakeDamage→内部 TakeBodyDamage"被重复乘 1.2（双倍增伤 bug）。
//   脆弱集以僵尸地址为键，轮询帧每帧重建 + onZombieRemove 兜底清理，此处只读。
// ★ 返回 0 = 毁灭菇领域已把这笔伤害改走 TakeBodyDamage 直接结算本体，
//   trampoline 收到 0 提前 ret（跳过原版 TakeDamage，防 0 伤害走原路径触发闪白/状态副作用）。
//   毁灭领域穿甲对防爆门僵尸无效（防爆门限伤代码优先级更高）。
static int __cdecl CapBlastDoorDamageWithVuln(DWORD zombieAddr, int damage)
{
	__try
	{
		if (zombieAddr && g_iceVulnZombies.count(zombieAddr) && g_iceVulnPercent > 0)
			damage = damage * (100 + g_iceVulnPercent) / 100; // +20% 结算（先于限伤）
		if (zombieAddr && !g_doomDomainZombies.empty()
			&& g_doomDomainZombies.count(zombieAddr)
			&& g_blastDoorZombies.count(MemSafeRead<int>(zombieAddr + 0x158)) == 0)
		{
			DoomBurnRegister(zombieAddr);          // 紫焰登记（POD 写，事件帧安全）
			DoomDomainPierce(zombieAddr, damage); // 无视一类/二类防具，直接结算本体
			return 0;                             // trampoline 提前 ret，跳过原版 TakeDamage
		}
		return CapBlastDoorDamage(zombieAddr, damage);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		return damage; // 任何异常一律放行（保底不破坏游戏）
	}
}

// 安装两个限伤 hook；返回 true=至少装好一个。运行时序言与预期不符时跳过并记日志。
static bool InstallBlastDamageHooks()
{
	// 预期运行时序言（与文件字节一致；不一致 = 该区域运行时解密/变换 → 不可 hook）
	static const BYTE kExpected[2][7] = {
		{ 0x51, 0x8B, 0x4E, 0x28, 0x83, 0xF9, 0x10 }, // TakeDamage:  push ecx; mov ecx,[esi+0x28]; cmp ecx,0x10
		{ 0x83, 0xEC, 0x08, 0x8B, 0x44, 0x24, 0x14 }, // TakeBodyDamage: sub esp,8; mov eax,[esp+0x14]
	};
	static const DWORD kAddrs[2] = { 0x5317C0, 0x5312D0 };
	static const BYTE kDamageOff[2] = { 0x24, 0x28 }; // pushad 帧中伤害槽位（[esp+0x24]/[esp+0x28]）
	static const bool kZombieInEsi[2] = { true, false }; // TakeDamage: esi=this；TakeBodyDamage: [esp+0x24]=this

	bool anyInstalled = false;
	for (int i = 0; i < 2; i++)
	{
		BYTE raw[8];
		PVZ::Memory::ReadArray<BYTE>(kAddrs[i], raw, 7);
		if (memcmp(raw, kExpected[i], 7) != 0)
		{
			continue; // 跳过该 hook（不装=无限伤但绝不崩溃）
		}
		// i==0(TakeDamage) 支持毁灭菇领域提前返回：helper 返回 0 → 跳过原版代码直接 ret 4
		//（TakeDamage 尾部 ret 4 已反汇编核实：stdcall 单栈参 damage；0 伤害走原路径
		//  会触发闪白 [esi+0x54]=25 等副作用，故必须提前返回而非回写 0）
		bool doomEarlyReturn = (i == 0);

		int tramp = (int)TRAMPOLINE_ALLOC();
		if (tramp == 0)
			continue;
		BYTE tp[128];
		int p = 0;
		auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
		// rel32 必须用 DWORD(无符号) 运算：VirtualAlloc 可能返回高地址（int 视为负数）会溢出
		auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
		auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

		tp[p++] = 0x60;                                  // pushad
		if (kZombieInEsi[i])
		{
			tp[p++] = 0x8B; tp[p++] = 0xC6;              // mov eax, esi（僵尸）
		}
		else
		{
			tp[p++] = 0x8B; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x24; // mov eax,[esp+0x24]（僵尸）
		}
		tp[p++] = 0x8B; tp[p++] = 0x4C; tp[p++] = 0x24; tp[p++] = kDamageOff[i]; // mov ecx,[esp+0xXX]（伤害）
		tp[p++] = 0x51;                                  // push ecx（伤害, arg2）
		tp[p++] = 0x50;                                  // push eax（僵尸, arg1）
		putRelCall((DWORD)((i == 0) ? (DWORD)CapBlastDoorDamageWithVuln : (DWORD)CapBlastDoorDamage)); // i==0(TakeDamage)走脆弱+领域穿甲+限伤；i==1(TakeBodyDamage)走纯限伤
		tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x08;  // add esp,8（清参数）
		if (doomEarlyReturn)
		{
			tp[p++] = 0x83; tp[p++] = 0xF8; tp[p++] = 0x00; // cmp eax,0（0=领域已改走本体结算）
			tp[p++] = 0x74; tp[p++] = 0x11;                 // je handled（rel8=17：跳过下面 mov+popad+原7字节+jmp）
		}
		tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = kDamageOff[i]; // mov [esp+0xXX],eax（写回限伤值）
		tp[p++] = 0x61;                                  // popad
		memcpy(tp + p, raw, 7); p += 7;                  // 原7字节（完整指令：1+3+3）
		putRelJmp(kAddrs[i] + 7);                        // 跳回 hook 点之后
		if (doomEarlyReturn)
		{
			tp[p++] = 0x61;                                  // handled: popad（此时 esp=入口 esp，栈顶=返回地址）
			tp[p++] = 0xC2; tp[p++] = 0x04; tp[p++] = 0x00;  // ret 4（清除 damage 栈参，模拟 TakeDamage 正常返回）
		}

		PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
		int hookOff = tramp - ((int)kAddrs[i] + 5);
		BYTE hook[5] = { 0xE9 };
		memcpy(hook + 1, &hookOff, 4);
		PVZ::Memory::WriteArray<BYTE>(kAddrs[i], hook, 5);
		// 写回验证（确认 hook 真正写入，失败则判定未安装）
		{
			BYTE verify[5];
			PVZ::Memory::ReadArray<BYTE>(kAddrs[i], verify, 5);
			if (memcmp(verify, hook, 5) != 0)
				continue; // 写入失败：不标记安装成功
		}
		anyInstalled = true;
	}
	return anyInstalled;
}

// ==================== 防爆门僵尸：灰烬化灰拦截 hook ====================
// ★★★ 灰烬爆炸有两条伤害路径（反汇编 0x41D8A0 爆炸函数确认）：
//   1) TakeDamage(1800, flags=0x12) —— 已被上面的限伤 hook 覆盖（200 → 防具吸收，本体安全）
//   2) ApplyBurn(0x532B70) 直接化灰 —— 不走任何伤害结算，防爆门僵尸被一击化灰！
//      （0x41D8A0 的 [ebp+0x20] 参数非 0 时走此分支，樱桃/毁灭/倭瓜等灰烬植物都会用）
// 修复：hook ApplyBurn 入口（ecx=this）。防爆门且铁门（盾牌）存在 → 拦截化灰，
//   改为对僵尸施加 TakeDamage(限伤值, 0x12)（原灰烬标志：防具+本体同时结算，
//   与"原版灰烬伤害同时对防具和本体造成伤害"的机制一致，但每层限伤 200）；
//   铁门已破或非防爆门 → 放行原化灰逻辑。
// 注：TakeDamage 已被本 DLL 限伤 hook 覆盖，此处调用它不会再递归（200<=上限快速放行）。

// ApplyBurn 拦截判定（trampoline 直接 rel32 call，__cdecl；参数：zombieAddr）
// 返回 -1 = 不拦截（放行原化灰逻辑）；否则返回应施加的限伤伤害值（拦截化灰）
static int __cdecl BlastBurnCheck(DWORD zombieAddr)
{
	__try
	{
		if (g_blastDoorZombies.empty())
			return -1; // 场上无防爆门僵尸：全部正常化灰（快速路径）
		if (!zombieAddr)
			return -1;
		int zid = MemSafeRead<int>(zombieAddr + 0x158);
		if (g_blastDoorZombies.count(zid) == 0)
			return -1; // 非防爆门僵尸：正常化灰
		// 铁门（盾牌）生命 > 0 才拦截；铁门已破 → 解除保护，正常化灰
		if (MemSafeRead<int>(zombieAddr + 0xDC) <= 0)
			return -1;
		return g_blastMaxDamage; // 拦截化灰，改施加上限伤害（0x12 标志走原灰烬结算路径）
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		return -1; // 任何异常一律放行（保底不破坏游戏）
	}
}

// 安装 ApplyBurn(0x532B70) 化灰拦截 hook；返回 true=安装成功
// trampoline 布局：
//   pushad; push ecx; call BlastBurnCheck; add esp,4; cmp eax,-1; je ORIG
//   ; BLOCKED（拦截）：
//   mov [scratchDmg],eax; mov [scratchEsi],esi   ; 暂存限伤值 + 调用方 esi
//   popad                                        ; 恢复全部寄存器（ecx=僵尸）
//   mov eax,[scratchDmg]; push eax               ; [esp]=限伤伤害
//   mov eax,0x12                                 ; 灰烬标志（同时结算防具与本体）
//   mov esi,ecx                                  ; this=僵尸
//   call 0x5317C0                                ; TakeDamage（已被限伤 hook 保护，无递归）
//   mov esi,[scratchEsi]                         ; 恢复调用方 esi（TakeDamage 会改写 esi）
//   ret                                          ; 返回原调用者（模拟 ApplyBurn 正常返回）
//   ; ORIG：
//   popad; 原6字节; jmp hookAddr+6
static bool InstallBlastBurnHook()
{
	DWORD hookAddr = 0x532B70; // Zombie::ApplyBurn
	static const BYTE kExpected[6] = { 0x55, 0x8B, 0xEC, 0x83, 0xE4, 0xF8 }; // push ebp; mov ebp,esp; and esp,-8

	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 6);
	if (memcmp(raw, kExpected, 6) != 0)
	{
		return false;
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return false;

	DWORD dmgScratchAddr = (DWORD)&g_blastBurnDmgScratch;
	DWORD esiScratchAddr = (DWORD)&g_blastBurnEsiScratch;

	BYTE tp[96];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                  // pushad
	tp[p++] = 0x51;                                  // push ecx（僵尸, arg）
	putRelCall((DWORD)&BlastBurnCheck);              // eax = -1 或限伤值
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;  // add esp,4
	tp[p++] = 0x83; tp[p++] = 0xF8; tp[p++] = 0xFF;  // cmp eax, -1
	int jeOrig = p;
	tp[p++] = 0x74; tp[p++] = 0x00;                  // je ORIG（回填）

	// ---- BLOCKED（拦截化灰，改为限伤伤害）----
	tp[p++] = 0xA3; put32((int)dmgScratchAddr);      // mov [scratchDmg], eax
	tp[p++] = 0x89; tp[p++] = 0x35; put32((int)esiScratchAddr); // mov [scratchEsi], esi
	tp[p++] = 0x61;                                  // popad（恢复全部寄存器，ecx=僵尸）
	tp[p++] = 0xA1; put32((int)dmgScratchAddr);      // mov eax, [scratchDmg]（限伤伤害）
	tp[p++] = 0x50;                                  // push eax → [esp]=伤害（TakeDamage 入口 [esp+4]=伤害）
	tp[p++] = 0xB8; tp[p++] = 0x12; tp[p++] = 0x00; tp[p++] = 0x00; tp[p++] = 0x00; // mov eax, 0x12（灰烬标志）
	tp[p++] = 0x8B; tp[p++] = 0xF1;                  // mov esi, ecx（this=僵尸）
	putRelCall(0x5317C0);                            // call Zombie::TakeDamage（已限伤，无递归）
	tp[p++] = 0x8B; tp[p++] = 0x35; put32((int)esiScratchAddr); // mov esi, [scratchEsi]（恢复调用方 esi）
	tp[p++] = 0xC3;                                  // ret（返回原调用者）

	// ---- ORIG（放行：恢复寄存器后执行原 6 字节）----
	*(BYTE*)(tp + jeOrig + 1) = (BYTE)(p - (jeOrig + 2)); // 回填 je rel8
	tp[p++] = 0x61;                                  // popad
	memcpy(tp + p, raw, 6); p += 6;                  // 原6字节（55 8B EC 83 E4 F8）
	putRelJmp(hookAddr + 6);                         // 跳回 hook 点之后

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	return true;
}

// ==================== 防爆门僵尸：大嘴花撕咬 / 磁力菇免疫 hook ====================
// 需求（2026-08-19 用户确认）：
//   1) 大嘴花对防爆门 = **像对巨人一样撕咬**（40/口掉血），不能一口吞。
//      实现：hook 0x461451（类型判定尾部 cmp eax,0x19），目标(esi)是防爆门 →
//      强制 dl=1 → 走原版完整巨人撕咬路径（0x46148E 动画 → 0x4614DC TakeDamage(40)）。
//      配合 0x46143C 索敌兜底（FindTargetZombie 对大嘴花可能返回 0 → 扫描防爆门）。
//   2) 磁力菇 = **不能吸防爆门的任何防具**（铁门/铁桶都不可被吸取）。
//      实现：hook 0x4620BD（找目标循环防具判定起点），目标(ebx)是防爆门 →
//      跳 0x46218F 跳过该僵尸 → 磁力菇找别的目标或待机。
// 历史教训：早期把"不能吸/不能吞"当成 bug 去加 hook 反而崩溃，正确需求是"免疫/撕咬"。
// 所有 hook 都在 0x46 植物区域（文件字节=运行时，仍做序言探测防意外）。

// 大嘴花目标兜底：当 FindTargetZombie 返回 0（找不到目标，实测大嘴花对类型6植物
// 的通用索敌会失败导致走咬合而非吞噬）时，扫描场上**同行**的防爆门返回最近的一个。
// 返回 0 = 没有防爆门可吞。
// ★行字段：GameObject::Row=+0x1C（大嘴花 Update 里 mov ecx,[edi+0x1C] 传给
//  FindTargetZombie 作 row 参数，铁证）；距离用 GameObject::ImageX(+8) 取整坐标。
// ★C2712：含 std::vector 局部对象（GetAllZombies）→ 内层函数做实际工作，外层包 __try
static DWORD FindBlastDoorTargetInner(DWORD plantAddr)
{
	if (g_blastDoorZombies.empty())
		return 0;
	int boardAddr = MemSafeRead<int>(PVZ_BASE + 0x768);
	if (!boardAddr)
		return 0;
	PVZ::Board board(boardAddr);
	if (!board.GetBaseAddress())
		return 0;
	int plantRow = 0;
	int plantImageX = 0;
	if (plantAddr)
	{
		plantRow = MemSafeRead<int>(plantAddr + 0x1C); // GameObject::Row（行）
		plantImageX = MemSafeRead<int>(plantAddr + 8); // GameObject::ImageX（取整X）
	}
	auto zombies = board.GetAllZombies();
	DWORD best = 0;
	float bestDist = 1e9f;
	for (auto& z : zombies)
	{
		if (z.NotExist)
			continue;
		int zaddr = z.GetBaseAddress();
		if (!zaddr)
			continue;
		int zid = MemSafeRead<int>(zaddr + 0x158);
		if (g_blastDoorZombies.count(zid) == 0)
			continue;
		// ★大嘴花只能咬/吞同行的目标：跨行的防爆门不候选
		if (plantAddr && MemSafeRead<int>(zaddr + 0x1C) != plantRow)
			continue;
		int zImageX = MemSafeRead<int>(zaddr + 8); // 僵尸 ImageX
		int d = zImageX - plantImageX;
		if (d < 0) d = -d;
		if ((float)d < bestDist)
		{
			bestDist = (float)d;
			best = (DWORD)zaddr;
		}
	}
	return best;
}

static DWORD __cdecl FindBlastDoorTarget(DWORD plantAddr)
{
	__try
	{
		return FindBlastDoorTargetInner(plantAddr);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		return 0;
	}
}

// 大嘴花目标判定：返回 true=目标是防爆门（强制可吞）
static int __cdecl IsBlastDoorTarget(DWORD zombieAddr)
{
	__try
	{
		if (g_blastDoorZombies.empty() || !zombieAddr)
			return 0;
		int zid = MemSafeRead<int>(zombieAddr + 0x158);
		return g_blastDoorZombies.count(zid) != 0 ? 1 : 0;
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		return 0;
	}
}

// 安装大嘴花"防爆门→巨人式撕咬" hook @0x461451（83 F8 19 75 02，rawLen=5）
// 位置：大嘴花 Update 状态0xA 的类型判定尾部（cmp eax,0x19; jne 0x461458），
//  0x461456 是 mov dl,1（巨人标志，仅类型 0x17/0x20/0x19 会走到）。
// ★需求：防爆门**不能被一口吞**，要像对巨人一样撕咬（40/口掉血）。
// ★★v6 终极方案（自研撕咬，不再复用原版路径）：
//   v5 走"原版完整巨人撕咬路径"（dl=1 → 0x46148E 动画准备），但防爆门场景
//   特性表[edi]+0x8C5==0 → 0x461497 jne 不跳 → 走原版从未走过的动画段
//   0x461499-0x4614D7（call 0x515020）→ 该动画函数破坏 ebp（tdEbp=0x28 铁证：
//   BLOCKED 入口 ebp=001AF9F0 正常、call TakeDamage 时 ebp=0x28）→ 大嘴花
//   epilogue mov esp,ebp 崩。skipanim(0x461490)/skipcall(0x4614D7) 拦截
//   均未能可靠拦住（崩溃轮依旧 tdEbp=0x28）。
//   → v6：BLOCKED 里 popad 后**自行构造 TakeDamage(40) 调用 + 设状态 0xC**，
//   直接 jmp 0x4614EC（epilogue 起点）——0x46148A 之后原版代码全不执行，
//   0x515020 物理上不会运行，ebp 全程干净。诊断移进 pushad 帧内（popad 兜底）。
// 布局：
//   pushad; push eax(类型); push esi(僵尸); push edi(大嘴花); call ChomperShouldBiteOverride;
//          add esp,0xC; test al,al; jnz BLOCKED
//   ORIG: popad; cmp eax,0x17; je 0x461456(mov dl,1); jmp 0x46144C(cmp eax,0x20)
//   BLOCKED: [pushad 帧内不 popad] push esi(僵尸); push edi(大嘴花); call ChomperBiteDamage;
//          add esp,8; push eax(伤害); xor eax,eax; call TakeDamage(0x5317C0);
//            mov [edi+0x3C],0xC; jmp 0x4614EC（epilogue 起点，mov esp,ebp 清 pushad 残留）
// ★hook 取 0x461447（cmp eax,0x17，所有咬合候选必经且非跳转目标），一次抓 防爆门+5阶巨人；
//   0阶巨人/普通僵尸 ORIG 走原生完整流程。避开 0x461456(0x458 是其它逻辑跳转目标，勿占用)。
static bool InstallBlastChomperHook()
{
	DWORD hookAddr = 0x461447; // Chomper Update 咬合判定: cmp eax,0x17; je 0x461456
	static const BYTE kExpected[5] = { 0x83, 0xF8, 0x17, 0x74, 0x0A };

	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 5);
	if (memcmp(raw, kExpected, 5) != 0)
	{
		return false;
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return false;

	BYTE tp[96];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                  // pushad
	tp[p++] = 0x50;                                  // push eax（arg3=类型；eax 出 0x461444 后=类型未变）
	tp[p++] = 0x56;                                  // push esi（arg2=僵尸）
	tp[p++] = 0x57;                                  // push edi（arg1=大嘴花）
	putRelCall((DWORD)&ChomperShouldBiteOverride);   // eax = 1(防爆门 或 5阶巨人)→走自研撕咬
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x0C;  // add esp,0xC（清3参数）
	tp[p++] = 0x84; tp[p++] = 0xC0;                  // test al, al
	int jnzBlocked = p;
	tp[p++] = 0x75; tp[p++] = 0x00;                  // jnz BLOCKED（回填）

	// ---- ORIG（非防爆门且非5阶巨人：原逻辑）----
	tp[p++] = 0x61;                                  // popad
	tp[p++] = 0x83; tp[p++] = 0xF8; tp[p++] = 0x17;  // cmp eax, 0x17（原指令）
	tp[p++] = 0x0F; tp[p++] = 0x84;                  // je 0x461456（原 je 语义，rel32）
	put32(0x461456 - ((DWORD)tramp + (DWORD)p + 4));
	tp[p++] = 0xE9;                                  // jmp 0x46144C（原 fall-through: cmp eax,0x20）
	put32(0x46144C - ((DWORD)tramp + (DWORD)p + 4));

	// ---- BLOCKED（防爆门：自研撕咬，完全绕开 0x46148A 之后的原版代码）----
	// ★★★ v6 终极方案：v4/v5/v5.2/v5.3 复用原版巨人撕咬路径，但防爆门场景
	//   特性表[edi]+0x8C5==0 → 0x461497 jne 不跳 → 走原版从未走过的动画段
	//   0x461499-0x4614D7（call 0x515020）→ 该动画函数破坏 ebp（tdEbp=0x28 铁证：
	//   BLOCKED 入口 ebp=001AF9F0 正常、call TakeDamage 时 ebp=0x28）→
	//   大嘴花 epilogue mov esp,ebp 崩。skipanim(0x461490)/skipcall(0x4614D7)
	//   拦截均未能可靠拦住（判定偶发返回 0 走 ORIG）。
	//   → 不再复用原版路径：popad 后自行构造 TakeDamage(40) 调用 + 设状态 0xC，
	//   直接跳到 epilogue 起点 0x4614EC。0x515020 物理上不会执行，ebp 全程干净，
	//   TakeDamage 保存/恢复的 ebp 是正确的帧指针 → 不再崩溃。
	*(BYTE*)(tp + jnzBlocked + 1) = (BYTE)(p - (jnzBlocked + 2)); // 回填 jnz → BLOCKED
	// ★自研撕咬：TakeDamage(伤害, flags=0)（esi=僵尸 this；ret 4 自动清栈）
	//  ★基于等阶：0-4阶伤害=40（原版）；5阶=对"护甲+本体"10%百分比（保底40），防爆门封顶200。
	//    ChomperBiteDamage(plant=edi, zombie=esi) __cdecl，调用仅破坏 eax/ecx/edx，esi/edi 保留
	tp[p++] = 0x56;                                  // push esi（僵尸, arg2）
	tp[p++] = 0x57;                                  // push edi（大嘴花, arg1）
	putRelCall((DWORD)&ChomperBiteDamage);           // eax = 撕咬伤害（0-4阶40）
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x08;  // add esp,8（清两个参数）
	tp[p++] = 0x50;                                  // push eax（伤害 → call TakeDamage 后 [esp+4]）
	tp[p++] = 0x33; tp[p++] = 0xC0;                  // xor eax,eax（flags=0）
	putRelCall(0x5317C0);                            // call Zombie::TakeDamage（esi=僵尸 this）
	tp[p++] = 0xC7; tp[p++] = 0x47; tp[p++] = 0x3C; tp[p++] = 0x0C; tp[p++] = 0x00; tp[p++] = 0x00; tp[p++] = 0x00; // mov dword [edi+0x3C],0xC（状态0xC，同原版 0x4614E5）
	putRelJmp(0x4614EC);                             // jmp epilogue 起点（pop edi; pop esi; pop ebx; mov esp,ebp; pop ebp; ret）

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	return true;
}

// 安装"植物数组已释放对象"防御守卫 @0x463920（8B 0B 8B 83 94...，rawLen=5，正常跳回 hookAddr+5）
// ★★★崩溃现场（多次复现 0xC0000005 @0x463928, fault=0x820）：某植物对象首字段被清 0（[ebx]==0，
//   [ebx+0x94]==-1，典型的是堆损坏后残留），原生 0x463920（按 [plant+0x94] 索引 [plant]+0x820 数组）
//   在此解引用 → 崩。0x463920 的返回值被调用者(0x463E40 等)丢弃，故对非法对象安全返回 0 即可防崩。
//  → 本守卫：检测到 [ebx]==0 或 [ebx+0x94]==-1 → 直接 mov eax,0; ret（跳过整个函数，调用方忽略返回）。
//  → 合法对象走原逻辑，瞬时开销极小。
static bool InstallBlastFreedPlantGuard()
{
	DWORD hookAddr = 0x463920;
	static const BYTE kExpected[5] = { 0x8B, 0x0B, 0x8B, 0x83, 0x94 };

	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 5);
	if (memcmp(raw, kExpected, 5) != 0)
		return false;

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return false;

	BYTE tp[64];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	// mov ecx,[ebx]; test ecx,ecx; jz SKIP
	tp[p++] = 0x8B; tp[p++] = 0x0B;
	tp[p++] = 0x85; tp[p++] = 0xC9;
	int jzSkip = p; tp[p++] = 0x74; tp[p++] = 0x00;
	// 合法：重建原两条指令 mov eax,[ebx+0x94]; mov edx,[ecx+0x820]; jmp 0x46392E（继续原生）
	tp[p++] = 0x8B; tp[p++] = 0x83; tp[p++] = 0x94; tp[p++] = 0x00; tp[p++] = 0x00; tp[p++] = 0x00;
	tp[p++] = 0x8B; tp[p++] = 0x91; tp[p++] = 0x20; tp[p++] = 0x08; tp[p++] = 0x00; tp[p++] = 0x00;
	putRelJmp(0x46392E);
	// SKIP: 已释放/损坏对象 → mov eax,0; ret（返回被调用方忽略，安全防崩）
	int skipPos = p;
	*(BYTE*)(tp + jzSkip + 1) = (BYTE)(skipPos - (jzSkip + 2));
	tp[p++] = 0xB8; tp[p++] = 0x00; tp[p++] = 0x00; tp[p++] = 0x00; tp[p++] = 0x00; // mov eax,0
	tp[p++] = 0xC3; // ret

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	return true;
}

// 安装"植物数组已释放/游离对象"防御守卫 · Plant::Update 尾部 @0x463ED2（E8 D9 0E 00 00 = call 0x464DB0）
// ★★★崩溃现场（VEH 日志多次复现，含"游戏中频繁触发"）：EIP=0x0046441F，code@eip=8B 90 20 08 00 00
//   （mov edx,[eax+0x820]），fault=0x00000820 —— eax = [this] = 0，即 **被遍历到的植物对象首字段
//   (LawnApp*) 已被清 0（或 this 本身是游离/栈残值）**，随后 0x464410 用 [this]+0x820 解引用 → 崩。
//   调用链（栈帧偏移已按崩溃栈 dump 逐槽核对）：
//     Board::UpdateGameObjects(0x4130D0) → 植物 DataArray 迭代器(0x41C950)
//       → Plant::Update(0x463E40，this=EAX/EBX) → 0x464DB0 → 0x464480 / 0x464410 ← 崩在这
//   ★这与本文件 0x463920 守卫（InstallBlastFreedPlantGuard）是**同一崩溃类**：同为
//     "植物首字段被清 0 后仍被更新"，fault 地址同为 0x820；0x463920 只覆盖了它之后的路径，
//     覆盖不到 0x464DB0 这条更早的路径 —— 本守卫就是补这个缺口。
// ★0x464DB0 全 exe 只有一个调用点（0x463ED2，已用 exe 全量扫描 call 站点确认），是干净的收口点：
//     合法  → 原样 call 0x464DB0; ret        （回到 0x463ED7，行为与未打补丁完全一致）
//     非法  → pushad 记账 → pop 掉本层返回地址(0x463ED7) → pop 恢复 Plant::Update 保存的 EBX
//             → ret  （等价于 Plant::Update 正常返回 0x4130F9；**顺带把可能已被改坏的 EBX 修回 Board**）
//   校验（任一不过=跳过本株本帧更新，游戏其余部分照常）：
//     ① this >= 0x10000                       —— 排除 0/低位野指针
//     ② LawnApp = [0x6A9EC0] 非空
//     ③ Board   = [LawnApp+0x768] 非空
//     ④ this ∈ [Board+0xAC, Board+0xAC + [Board+0xB0]*0x14C)  —— 必须落在植物 DataArray 内
//     ⑤ [this] >= 0x10000                     —— 首字段必须是合理指针（崩溃现场此处为 0）
//   寄存器：只动 EAX/ECX/EDX（call 约定内易失寄存器，原版该点后本就不可依赖）；
//     EBX/ESI/EDI/EBP/ESP 全部严格保持；EBX 由 pop 显式复原。
static volatile LONG g_plantFreedTailHits = 0;
static DWORD g_plantFreedTailLast = 0;

// 记账（__cdecl；被 naked stub 用 pushad/popad 包裹调用，内层不得依赖任何寄存器值）
static void PlantFreedTailGuardNote(DWORD plantPtr)
{
	g_plantFreedTailHits++;
	if (g_plantFreedTailLast == plantPtr) return;   // 同一指针只记一次，防刷屏
	g_plantFreedTailLast = plantPtr;
	if (g_plantFreedTailHits > 64) return;
	CrashStr("\r\n---- PLANTGUARD blocked ----\r\n");
	CrashLineAddr("plant", plantPtr);
	CrashStr("step="); CrashStr(g_crashStep ? g_crashStep : "?");
	CrashStr("\r\n");
}

static bool InstallBlastFreedPlantTailGuard()
{
	DWORD hookAddr = 0x463ED2;
	static const BYTE kExpected[5] = { 0xE8, 0xD9, 0x0E, 0x00, 0x00 };   // call 0x464DB0
	BYTE raw[5];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 5);
	if (memcmp(raw, kExpected, 5) != 0)
	{
		CrashStr("HOOKSKIP name=PlantFreedTail site=0x463ED2 (bytes changed - modifier?)\r\n");
		return false;
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0) return false;

	BYTE tp[128];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	// ★★★ 所有条件跳转位移统一"回填"（原来写死 0x42/0x30/0x26/0x16/0x12/0x08）。
	//    原因：FALLBACK 从 3 字节(`ret`)变为 5 字节(`jmp rel32`)后，后面每个标号的绝对
	//    偏移都会后移 2 —— 写死的位移会指到错误位置（正是本项目 2026-10-07 排查到的缺陷来源）。
	int jbA1 = 0, jzF1 = 0, jzF2 = 0, jbA2 = 0, jaeA1 = 0, jbA3 = 0;

	// ① cmp eax,0x10000 ; jb ABORT
	tp[p++] = 0x3D; put32(0x10000);
	jbA1 = p; tp[p++] = 0x72; tp[p++] = 0x00;
	// ② mov ecx,[0x6A9EC0](LawnApp) ; test ecx,ecx ; jz FALLBACK
	tp[p++] = 0x8B; tp[p++] = 0x0D; put32(0x6A9EC0);
	tp[p++] = 0x85; tp[p++] = 0xC9;
	jzF1 = p; tp[p++] = 0x74; tp[p++] = 0x00;
	// ③ mov ecx,[ecx+0x768](Board) ; test ecx,ecx ; jz FALLBACK
	tp[p++] = 0x8B; tp[p++] = 0x89; put32(0x768);
	tp[p++] = 0x85; tp[p++] = 0xC9;
	jzF2 = p; tp[p++] = 0x74; tp[p++] = 0x00;
	// ④ mov edx,[ecx+0xAC](base) ; mov ecx,[ecx+0xB0](count) ; imul ecx,ecx,0x14C ; add ecx,edx(end)
	tp[p++] = 0x8B; tp[p++] = 0x91; put32(0xAC);
	tp[p++] = 0x8B; tp[p++] = 0x89; put32(0xB0);
	tp[p++] = 0x69; tp[p++] = 0xC9; put32(0x14C);
	tp[p++] = 0x03; tp[p++] = 0xCA;
	tp[p++] = 0x3B; tp[p++] = 0xC2;                  // cmp eax,edx(base)
	jbA2 = p; tp[p++] = 0x72; tp[p++] = 0x00;        // jb ABORT
	tp[p++] = 0x3B; tp[p++] = 0xC1;                  // cmp eax,ecx(end)
	jaeA1 = p; tp[p++] = 0x73; tp[p++] = 0x00;       // jae ABORT
	// ⑤ mov edx,[eax] ; cmp edx,0x10000 ; jb ABORT
	tp[p++] = 0x8B; tp[p++] = 0x10;
	tp[p++] = 0x81; tp[p++] = 0xFA; put32(0x10000);
	jbA3 = p; tp[p++] = 0x72; tp[p++] = 0x00;

	// ---- FALLBACK（合法植物：等价于原版 `call 0x464DB0` 之后继续执行 0x463ED7）----
	int fbPos = p;
	*(BYTE*)(tp + jzF1 + 1) = (BYTE)(fbPos - (jzF1 + 2));
	*(BYTE*)(tp + jzF2 + 1) = (BYTE)(fbPos - (jzF2 + 2));
	tp[p++] = 0xB9; put32(0x464DB0);                 // mov ecx,0x464DB0
	tp[p++] = 0xFF; tp[p++] = 0xD1;                  // call ecx
	// ★★ 必须是 jmp 0x463ED7，不能是裸 `ret`：
	//    本站点是 Plant::Update **函数内部的 call**，不是函数入口。Plant::Update 全程
	//    只有入口那一次 `push ebx`（0x463E40），线性反汇编可证 —— 所以执行到 0x463ED2 时
	//    [esp] = 被保存的 EBX、[esp+4] = Plant::Update 的返回地址 0x4130F9。
	//    裸 `ret` 会弹出 [esp] = 保存的 EBX（调用方 EBX，通常是 Board 指针）当返回地址
	//    → 跳进堆数据执行 → "EBP=0、EIP 落在堆区"的跳飞崩溃。
	//    对照同文件 InstallBlastSkipCallHook（同为 mid-function call 站点）的正确写法：
	//      putRelCall(0x515020); putRelJmp(hookAddr + 5);
	putRelJmp(0x463ED7);                             // 跳回「原 call 的下一条」

	// ---- ABORT（非法植物：跳过本株本帧，等价于让 Plant::Update 正常返回）----
	int abPos = p;
	*(BYTE*)(tp + jbA1 + 1) = (BYTE)(abPos - (jbA1 + 2));
	*(BYTE*)(tp + jbA2 + 1) = (BYTE)(abPos - (jbA2 + 2));
	*(BYTE*)(tp + jaeA1 + 1) = (BYTE)(abPos - (jaeA1 + 2));
	*(BYTE*)(tp + jbA3 + 1) = (BYTE)(abPos - (jbA3 + 2));
	tp[p++] = 0x60;                                  // pushad（记账用，保护全部寄存器）
	tp[p++] = 0x50;                                  // push eax(plant)
	putRelCall((DWORD)&PlantFreedTailGuardNote);
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;  // add esp,4
	tp[p++] = 0x61;                                  // popad
	// ★★ 只需一次 pop ebx：弹掉"被保存的 EBX"并复原；随后 ret 弹 0x4130F9 回到
	//    Board::UpdateGameObjects 的植物循环。原来多了一次 `pop eax`（基于"call 已压
	//    返回地址"的错误假设）→ EBX 被写成返回地址、ret 弹到栈里别的内容 → 跳飞。
	tp[p++] = 0x5B;                                  // pop ebx（复原调用方 EBX）
	tp[p++] = 0xC3;                                  // ret → 0x4130F9

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);

	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	// ★ 写回验证：本安装点原来没有校验（WriteArray 底层是 WriteProcessMemory，返回 FALSE
	//   时被忽略）→ 写失败也 return true，外面就以为"守卫已装"，实际完全没生效。
	//   加一次回读 + 留痕，才能判定守卫到底有没有真的挂上去。
	{
		BYTE verify[5];
		PVZ::Memory::ReadArray<BYTE>(hookAddr, verify, 5);
		if (memcmp(verify, hook, 5) != 0)
		{
			CrashStr("HOOKFAIL name=PlantFreedTail site=0x463ED2 (write not effective)\r\n");
			return false;
		}
	}
	return true;
}

// 安装容器"空虚表派发"防御守卫 hook @0x565A53（8B 08 8B 51 08，rawLen=5，跳回 0x565A58）
// ★崩溃根因（0x565A55，进关卡读档瞬间复现）：游戏内某容器遍历元素时取元素虚表并派发：
//     mov eax,[ebx+eax]   (元素指针)
//     mov ecx,[eax]       (ecx = 元素虚表)
//     mov edx,[ecx+8]     ← 0x565A55 在此崩溃：元素虚表被清 0（ecx=0）→ 读 [0x8] 访问违例
//   症状特征 = 空指针"虚表调用"，与 0x463928（已释放植物）同属"游离/清零对象被遍历"崩溃类。
// 修复：拦截 0x565A53 段，元素虚表([eax]) 为 0 时跳过本次虚调用直进下一元素（0x565A5B），
//   合法路径重建原 5 字节后 jmp 0x565A58（push eax; call edx; 继续原生），寄存器语义完全一致。
// 布局：
//   mov ecx,[eax]; test ecx,ecx; jz SKIP
//   合法：mov edx,[ecx+8]; jmp 0x565A58
//   SKIP: jmp 0x565A5B（跳过本次派发，处理下一元素）
static bool InstallNullVtableDispatchGuard()
{
	DWORD hookAddr = 0x565A53;
	static const BYTE kExpected[5] = { 0x8B, 0x08, 0x8B, 0x51, 0x08 }; // mov ecx,[eax]; mov edx,[ecx+8]

	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 5);
	if (memcmp(raw, kExpected, 5) != 0)
		return false;

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return false;

	BYTE tp[64];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	// mov ecx,[eax]; test ecx,ecx; jz SKIP（虚表为 0 → 跳过）
	tp[p++] = 0x8B; tp[p++] = 0x08;                 // mov ecx,[eax]
	tp[p++] = 0x85; tp[p++] = 0xC9;                 // test ecx,ecx
	int jzSkip = p; tp[p++] = 0x74; tp[p++] = 0x00; // jz SKIP（回填）
	// 虚表有效：重建原两条指令后 jmp 0x565A58（push eax; call edx; 继续原生派发）
	tp[p++] = 0x8B; tp[p++] = 0x51; tp[p++] = 0x08; // mov edx,[ecx+8]
	putRelJmp(0x565A58);
	// SKIP：空虚表元素 → 跳过本次虚调用，jmp 0x565A5B（下一元素 / 循环尾）
	int skipPos = p;
	*(BYTE*)(tp + jzSkip + 1) = (BYTE)(skipPos - (jzSkip + 2));
	putRelJmp(0x565A5B);

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	// 写回验证（确认 hook 真正写入，失败则判定未安装）
	{
		BYTE verify[5];
		PVZ::Memory::ReadArray<BYTE>(hookAddr, verify, 5);
		if (memcmp(verify, hook, 5) != 0)
			return false;
	}
	return true;
}
// 安装大嘴花"防爆门跳过撕咬动画" hook @0x461490（80 B8 C5 08 00 00 00 cmp byte [eax+0x8C5],0，rawLen=5，跳回 hookAddr+7）
// ★★★崩溃根因（v5.2 诊断铁证）：撕咬动画段 `0x4614D7 call 0x515020` 在防爆门场景
//  破坏 ebp（tdEbp=0x28 日志证明：BLOCKED 入口 ebp=001AF9F0 正常，call TakeDamage 时
//  ebp=0x28）→ 大嘴花 epilogue mov esp,ebp 崩。原版咬巨人时特性表[edi]+0x8C5≠0
//  （0x461497 jne 0x4614DC）跳过动画直接伤害——防爆门场景 0x8C5==0 走了从未被
//  原版走过的动画路径（0x515020 内部 eax=动画ID=1 时野指针）。
// 修复：目标(esi)是防爆门 → 跳过 0x461499-0x4614D7 动画准备段，直接 jmp 0x4614DC
//  （push 0x28; TakeDamage(40); 状态0xC）——伤害/状态不变，仅省去动画。
// 布局：
//   pushad; push esi; call IsBlastDoorTarget; add esp,4; test al,al; jz ORIG
//   BLOCKED: popad; jmp 0x4614DC（直接伤害段）
//   ORIG: popad; cmp byte [eax+0x8C5],0; jne 0x4614DC(rel32); jmp 0x461499（原动画段）
static bool InstallBlastSkipAnimHook()
{
	DWORD hookAddr = 0x461490; // Chomper Update: cmp byte [eax+0x8C5],0（0x46148E mov eax,[edi] 后）
	static const BYTE kExpected[5] = { 0x80, 0xB8, 0xC5, 0x08, 0x00 };

	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 5);
	if (memcmp(raw, kExpected, 5) != 0)
	{
		return false;
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return false;

	BYTE tp[96];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                  // pushad
	tp[p++] = 0x56;                                  // push esi（目标僵尸, arg）
	putRelCall((DWORD)&IsBlastDoorTarget);           // eax = 1(防爆门)
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;  // add esp,4
	tp[p++] = 0x84; tp[p++] = 0xC0;                  // test al, al
	int jzOrig = p;
	tp[p++] = 0x74; tp[p++] = 0x00;                  // jz ORIG（回填）

	// ---- BLOCKED（防爆门：跳过动画段，直接伤害段 0x4614DC）----
	tp[p++] = 0x61;                                  // popad（恢复 esi=僵尸、edi=大嘴花、eax=[edi]）
	putRelJmp(0x4614DC);                             // push 0x28; TakeDamage(40); 状态0xC; epilogue

	// ---- ORIG（非防爆门：原逻辑）----
	*(BYTE*)(tp + jzOrig + 1) = (BYTE)(p - (jzOrig + 2)); // 回填 jz → ORIG
	tp[p++] = 0x61;                                  // popad
	// 原7字节 cmp byte [eax+0x8C5],0（重写）
	tp[p++] = 0x80; tp[p++] = 0xB8; tp[p++] = 0xC5; tp[p++] = 0x08; tp[p++] = 0x00; tp[p++] = 0x00; tp[p++] = 0x00;
	tp[p++] = 0x0F; tp[p++] = 0x85;                  // jne 0x4614DC（原 jne 语义，rel32）
	put32(0x4614DC - ((DWORD)tramp + (DWORD)p + 4));
	putRelJmp(0x461499);                             // 原 fall-through：动画准备段

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	// 写回验证（确认 hook 真正写入，失败则判定未安装）
	{
		BYTE verify[5];
		PVZ::Memory::ReadArray<BYTE>(hookAddr, verify, 5);
		if (memcmp(verify, hook, 5) != 0)
			return false;
	}
	return true;
}

// 安装大嘴花"拦截撕咬动画 call" hook @0x4614D7（E8 44 3B 0B 00 = call 0x515020，rawLen=5）
// ★v5.3：skipanim(0x461490) 拦截 tdEbp 仍=0x28（未生效）→ 直接拦截崩溃的 call 本身。
//  目标(esi)是防爆门 → 跳过 call 0x515020 直接 jmp 0x4614DC；非防爆门 → 重建 call。
// 布局：
//   pushad; push esi; call IsBlastDoorTarget; add esp,4; test al,al; jz ORIG
//   BLOCKED: popad; jmp 0x4614DC（跳过动画 call）
//   ORIG: popad; call 0x515020（重建，ecx=ebx/[esp]=float 由 popad 保留）; jmp 0x4614DC
static bool InstallBlastSkipCallHook()
{
	DWORD hookAddr = 0x4614D7; // Chomper Update: call 0x515020（撕咬动画）
	static const BYTE kExpected[5] = { 0xE8, 0x44, 0x3B, 0x0B, 0x00 };

	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 5);
	if (memcmp(raw, kExpected, 5) != 0)
	{
		return false;
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return false;

	BYTE tp[96];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                  // pushad
	tp[p++] = 0x56;                                  // push esi（目标僵尸, arg）
	putRelCall((DWORD)&IsBlastDoorTarget);           // eax = 1(防爆门)
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;  // add esp,4
	tp[p++] = 0x84; tp[p++] = 0xC0;                  // test al, al
	int jzOrig = p;
	tp[p++] = 0x74; tp[p++] = 0x00;                  // jz ORIG（回填）

	// ---- BLOCKED（防爆门：跳过 call 0x515020）----
	tp[p++] = 0x61;                                  // popad（恢复 esi=僵尸、edi=大嘴花）
	putRelJmp(0x4614DC);                             // push 0x28; TakeDamage(40); 状态0xC; epilogue

	// ---- ORIG（非防爆门：重建原 call）----
	*(BYTE*)(tp + jzOrig + 1) = (BYTE)(p - (jzOrig + 2)); // 回填 jz → ORIG
	tp[p++] = 0x61;                                  // popad（恢复 ecx=ebx、[esp]=float 参数）
	putRelCall(0x515020);                            // 原 call 0x515020（ret 4 清 float）
	putRelJmp(hookAddr + 5);                         // 跳回 0x4614DC（原 call 的下一条）

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	return true;
}

// ==================== 大嘴花（Chomper）等阶：撕咬伤害 + 消化计时 + 回血 ====================
// 需求（2026-08-31 用户确认）：
//   0阶 同原版；每次消化完成回复自身 100 血（0-5阶均生效）
//   1阶 血量上限→600；2阶 消化时间→30s级（config）；3阶 血量上限→1000；4阶 消化时间再缩短
//   5阶 对"无法吞咽的僵尸"(巨人/防爆门) 撕咬造成百分比伤害（护甲+本体10%，优先打护甲）；
//        伤害优先级低于防爆门限伤(200)：撕咬伤害 = clamp(10%伤害, 保底40, 防爆门限伤200)。
// 血量阶梯：300,600,600,1000,1000,1000；消化时间从 plant_attack_speed.ini 读取（秒）。
//
// ★原生反汇编结论（PlantsVsZombies.exe 0x461320 - 0x46150C）：
//   - 状态0xB(咀嚼,吞后) → 设状态0xD(消化) + AttributeCountdown(+0x54)=0xFA0(4000=40秒)
//   - 状态0xD 等 +0x54 归零 → 状态0xE → 状态1(就绪)。故"消化时间" = +0x54 的厘秒数。
//   - 撕咬伤害段 @0x4614DC：push 0x28(40); xor eax,eax; call TakeDamage(0x5317C0, esi=僵尸)
//   - 防爆门撕咬不走原生段（InstallBlastChomperHook BLOCKED 自研 TakeDamage 跳 epilogue）
// 大嘴花撕咬伤害计算（trampoline 直接 rel32 call；仅巨人/防爆门"撕咬"路径调用）
//  → 0-4阶返回40（原版）；5阶 = max( (BodyMax+HelmMax+ShieldMax+FlyingMax)*10% , 保底40 )，
//      若目标是防爆门且铁门未破，再封顶到 g_blastMaxDamage(200)。
static int __cdecl ChomperBiteDamage(DWORD plantAddr, DWORD zombieAddr)
{
	__try
	{
		int dmg = 40;
		if (!plantAddr || !zombieAddr)
			return dmg;
		int tier = 0;
		auto it = g_plantExperience.find(plantAddr);
		if (it != g_plantExperience.end())
			tier = GetPlantTier((int)SeedType::Chomper, it->second);
		if (tier >= 5)
		{
			int bodym = MemSafeRead<int>(zombieAddr + 0xCC);  // BodyMaxHealth
			int helmm = MemSafeRead<int>(zombieAddr + 0xD4);  // HelmMaxHealth
			int shldm = MemSafeRead<int>(zombieAddr + 0xE0);  // ShieldMaxHealth
			int flym  = MemSafeRead<int>(zombieAddr + 0xE8);  // FlyingMaxHealth
			dmg = (bodym + helmm + shldm + flym) * g_chomberBitePercent / 100;
			if (dmg < g_chomberBiteMinDamage)
				dmg = g_chomberBiteMinDamage;          // 保底40
			// 防爆门：伤害优先级低于"防爆门限伤"（铁门未破时封顶200）
			int zid = MemSafeRead<int>(zombieAddr + 0x158);
			if (g_blastDoorZombies.count(zid) != 0
				&& MemSafeRead<int>(zombieAddr + 0xDC) > 0
				&& dmg > g_blastMaxDamage)
				dmg = g_blastMaxDamage;
		}
		return dmg;
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		return 40; // 任何异常一律保底40（不破坏游戏）
	}
}

// 大嘴花撕咬路径预判（0x461447 hook BLOCKED 判定）：返回 1=走自研撕咬。
//  → 防爆门（各阶都吞不下，像巨人一样被咬）：必走自研撕咬（与旧行为一致）
//  → ★巨人型（类型 0x17 Gargantuar/0x20 Gigagargantuar/0x19 DrZomboss）：**所有等阶**都走自研撕咬
//   （原生巨人撕咬路径在本 mod 里经动画段会污染 ebp→0x4614F1 崩溃，自研绕开 0x515020 全程干净；
//    伤害由 ChomperBiteDamage 决定：0-4阶=40原版、5阶=10%）
//  → 否则返回 0：让原生逻辑走（普通僵尸该吞照吞，不受影响）
// ★仅 0x461447 入口调用：eax=类型([esi+0x24])，esi=僵尸，edi=大嘴花。
static int __cdecl ChomperShouldBiteOverride(DWORD plantAddr, DWORD zombieAddr, int type)
{
	int decision = 0;
	__try
	{
		if (!plantAddr || !zombieAddr)
			decision = 0;
		else
		{
			// 防爆门：吞不下，强撕咬（各等阶）
			int zid = MemSafeRead<int>(zombieAddr + 0x158);
			if (g_blastDoorZombies.count(zid) != 0)
				decision = 1;
			// 所有巨人型：吞不下，走自研撕咬（0-4=40原版，5=10%）
			else if (type == 0x17 || type == 0x20 || type == 0x19)
				decision = 1;
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		decision = 0; // 异常一律放行原生逻辑（保底不破坏游戏）
	}
	return decision;
}

// 安装磁力菇"跳过防爆门" hook @0x4620BD（8B 8B C4 00 00 00，rawLen=5，跳回 hookAddr+6）
// 位置：磁力菇 Update 找目标循环里的防具判定起点（mov ecx,[ebx+0xC4] 读 HelmType），
//  后续 0x4620C3/0x4620CD 判定 HelmType==2/3、ShieldType==1/3 → 跳 0x4620F4（可吸）。
// ★需求：**磁力菇不能吸防爆门的任何防具**（铁门/铁桶都不可被吸取）。
//  目标(ebx)是防爆门 → 跳 0x46218F（循环继续，跳过该僵尸不吸）→ 磁力菇找别的目标
//  或待机；防爆门完全免疫磁力菇。
// 布局：
//   pushad; push ebx; call IsBlastDoorTarget; add esp,4; test al,al; jz ORIG
//   BLOCKED: popad; jmp 0x46218F（循环继续）
//   ORIG: popad; mov ecx,[ebx+0xC4]; jmp 0x4620C3（原防具判定继续）
static bool InstallBlastMagnetBlockHook()
{
	DWORD hookAddr = 0x4620BD; // MagnetShroom Update: mov ecx,[ebx+0xC4]（HelmType 判定起点）
	static const BYTE kExpected[5] = { 0x8B, 0x8B, 0xC4, 0x00, 0x00 };

	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 5);
	if (memcmp(raw, kExpected, 5) != 0)
	{
		return false;
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return false;

	BYTE tp[96];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                  // pushad
	tp[p++] = 0x53;                                  // push ebx（僵尸, arg）
	putRelCall((DWORD)&IsBlastDoorTarget);           // eax = 1(防爆门)
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;  // add esp,4
	tp[p++] = 0x84; tp[p++] = 0xC0;                  // test al, al
	int jzOrig = p;
	tp[p++] = 0x74; tp[p++] = 0x00;                  // jz ORIG（回填）
	// ---- BLOCKED（防爆门：磁力菇跳过，不能吸）----
	tp[p++] = 0x61;                                  // popad（恢复寄存器）
	putRelJmp(0x46218F);                             // 循环继续（下一个僵尸）
	// ---- ORIG（非防爆门：原防具判定）----
	*(BYTE*)(tp + jzOrig + 1) = (BYTE)(p - (jzOrig + 2)); // 回填 jz → ORIG
	tp[p++] = 0x61;                                  // popad
	// ★原指令 mov ecx,[ebx+0xC4] 是 6 字节（8B 8B C4 00 00 00），必须完整复制，
	//  少第 6 字节会把后面的 jmp 首字节 E9 当成 disp32 → 指令错乱崩溃！
	tp[p++] = 0x8B; tp[p++] = 0x8B; tp[p++] = 0xC4; tp[p++] = 0x00; tp[p++] = 0x00; tp[p++] = 0x00;
	putRelJmp(hookAddr + 6);                         // 跳回 0x4620C3（cmp ecx,2）

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	return true;
}

// 安装大嘴花索敌兜底 hook @0x46143C（8B F0 32 D2 85 F6，rawLen=5，跳回 hookAddr+6）
// 位置：大嘴花状态0xA 里 FindTargetZombie 结果赋值点（mov esi,eax; xor dl,dl; test esi,esi）。
// 实测大嘴花对防爆门走"咬合"而非吞噬——通用索敌对大嘴花可能返回 0（目标丢失）。
// trampoline：eax(FindTargetZombie 结果)==0 时调用 FindBlastDoorTarget 扫描防爆门，
// 把 eax 写回 pushad 帧 → 原逻辑继续（esi=目标 → 0x461451 hook 强制 dl=1 撕咬）。
// ★跳回必须用 hookAddr+6=0x461442（原 6 字节指令 8B F0/32 D2/85 F6 之后的下一条
//  je 0x461458），跳到 0x461441 会落在 test 指令第二字节 0xF6 → 非法指令崩溃！
// 布局：
//   pushad; test eax,eax; jnz HAS; push edi; call FindBlastDoorTarget; add esp,4
//   HAS: mov [esp+0x1C],eax; popad; mov esi,eax; xor dl,dl; test esi,esi; jmp 0x461442
static bool InstallBlastFindHook()
{
	DWORD hookAddr = 0x46143C;
	static const BYTE kExpected[5] = { 0x8B, 0xF0, 0x32, 0xD2, 0x85 };

	BYTE raw[8];
	PVZ::Memory::ReadArray<BYTE>(hookAddr, raw, 5);
	if (memcmp(raw, kExpected, 5) != 0)
	{
		return false;
	}

	int tramp = (int)TRAMPOLINE_ALLOC();
	if (tramp == 0)
		return false;

	BYTE tp[96];
	int p = 0;
	auto put32 = [&](int v) { memcpy(tp + p, &v, 4); p += 4; };
	auto putRelCall = [&](DWORD target) { tp[p++] = 0xE8; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };
	auto putRelJmp = [&](DWORD target) { tp[p++] = 0xE9; put32((int)((DWORD)target - ((DWORD)tramp + (DWORD)p + 4))); };

	tp[p++] = 0x60;                                  // pushad
	tp[p++] = 0x85; tp[p++] = 0xC0;                  // test eax, eax
	int jnzHas = p;
	tp[p++] = 0x75; tp[p++] = 0x00;                  // jnz HAS（回填）
	// ---- 索敌失败：兜底找防爆门 ----
	tp[p++] = 0x57;                                  // push edi（大嘴花植物, arg）
	putRelCall((DWORD)&FindBlastDoorTarget);         // eax = 最近的防爆门（或 0）
	tp[p++] = 0x83; tp[p++] = 0xC4; tp[p++] = 0x04;  // add esp,4
	// ---- HAS：写回 eax 并继续原逻辑 ----
	*(BYTE*)(tp + jnzHas + 1) = (BYTE)(p - (jnzHas + 2)); // 回填 jnz → HAS
	tp[p++] = 0x89; tp[p++] = 0x44; tp[p++] = 0x24; tp[p++] = 0x1C; // mov [esp+0x1C], eax（pushad 帧 EAX 槽）
	tp[p++] = 0x61;                                  // popad
	tp[p++] = 0x8B; tp[p++] = 0xF0;                  // mov esi, eax（原指令）
	tp[p++] = 0x32; tp[p++] = 0xD2;                  // xor dl, dl（原指令）
	tp[p++] = 0x85; tp[p++] = 0xF6;                  // test esi, esi（原指令）
	putRelJmp(hookAddr + 6);                         // 原函数继续（0x461442: je 0x461458 等）

	PVZ::Memory::WriteArray<BYTE>(tramp, tp, p);
	int hookOff = tramp - ((int)hookAddr + 5);
	BYTE hook[5] = { 0xE9 };
	memcpy(hook + 1, &hookOff, 4);
	PVZ::Memory::WriteArray<BYTE>(hookAddr, hook, 5);
	return true;
}
// 直接写入出怪种类标志（Board + 0x54D4, 33字节）
static void SetZombieAllowedDirect(DWORD boardAddr, ZombieType::ZombieType* types, int count)
{
	for (int i = 0; i < 33; i++)
		MemSafeWrite<byte>(boardAddr + 0x54D4 + i, 0);
	for (int i = 0; i < count; i++)
		MemSafeWrite<byte>(boardAddr + 0x54D4 + (int)types[i], 1);
}

// Board 初始化完毕时仅设置延迟标志，不读取波次数据（此时波次尚未填充、AdventureLevel 也可能是 0）
void onBoardInitAfter(DWORD boardAddress)
{
	// 关卡切换时清空所有经验数据和植物状态（防止经验跨关卡继承）
	g_plantExperience.clear();
	g_projectileShooterMap.clear();
	g_lastDeathRow = -1;
	g_lastDeathExp = 0;
	g_upgradeSunflowerAddr = 0;
	g_upgradeRow = -1;
	g_pendingDoubleShotPlant = 0;
	g_pendingDoubleShotCD = 0;
	g_upgradeCol = -1;
	g_upgradeExp = 0;
	g_snowPeaFreezeProjectiles.clear();
	g_snowPeaIcicleProjectiles.clear();
	g_icicleHitZombies.clear();
	g_speedBoostedIcicles.clear();
	g_iciclePrevX.clear();
	g_repeaterIceFireProjectiles.clear();
	g_pendingIceFireDecelerates.clear();
	g_projectileFireStates.clear();
	g_justFiredProjectiles.clear();
	g_puffClusters.clear();
	g_puffToCell.clear();
	g_creatingExtraPuff = false;
	// 西瓜投手状态重置（连投槽位 + 大炮弹标记）
	MelonChainResetAll();
	MelonCannonResetAll();
	// 冰西瓜状态重置（普攻计数 + 待开大队列 + 小冰瓜标记）
	IceMelonResetShots();
	// 击退弹 Pow 特效队列清空
	g_kbPowFxQCount = 0;
	g_planternHealTimers.clear();
	g_scaredyStates.clear();
	g_potTopLastState.clear(); // 花盆装水贴图状态（内存池地址复用前必须清）
	CabbageClearMarks();
	g_cabbageExtraShooting = false;
	g_cabbageBounceCount = 0;
	g_cabbageNoBounce.clear();
	g_cabbageBounceArmCount = 0;
	g_bloverBoostEndTime = 0;
	g_pendingBloverTriggers.clear();

	// 撑杆司令：关卡切换清空全部状态（防跨关卡串数据）
	g_commanderWaveSlots.clear();
	g_lastSeenWave = -1;
	g_type3SeenInWave = 0;
	g_seenPoleVaulters.clear();
	g_commanderZombies.clear();
	g_cmdrBaseSpeed.clear();
	g_cmdrJumps.clear();
	g_cmdrLastState.clear();
	g_cmdrPrevX.clear();
	g_cmdrAnimSnap.clear();
	g_cmdrAnimSnapTaken.clear();
	g_cmdrRunFrames.clear();

	// 防爆门僵尸：关卡切换清空全部状态（hook 本身跨关卡保持，空集合时零开销）
	g_blastWaveSlots.clear();
	g_type6SeenInWave = 0;
	g_seenType6.clear();
	g_blastDoorZombies.clear();

	PVZ::Board board(boardAddress);
	if (!board.GetBaseAddress()) return;

	// 一律置位，真正的配置查找在 TryApplyWaveConfig（波次就绪、AdventureLevel 正确后）进行
	g_waveConfigPending = true;

	// ★ 2026-10-16：新关卡 → 图片加载限流计数清零（每个 loader 重新获得 600 次机会）。
	//   否则在选卡界面停留很久时，绘制路径上的 loader（大蒜箭头/磁力菇护盾）会把次数耗完，
	//   进关卡后即使贴图存在也不再尝试。
	for (int i = 0; i < IMGLOAD_SLOTS; i++)
		g_imgLoadTries[i] = 0;

	// 植物经验存档：挂起还原尝试（此时关卡可能仍在恢复植物，由轮询帧逐帧校验布局）
	PlantExpSaveBeginLevel();
}

// 在游戏对象更新时检查并应用出怪配置（此时波次已填充完毕）
static void TryApplyWaveConfig(DWORD boardAddress)
{
	if (!g_waveConfigPending) return;

	PVZ::Board board(boardAddress);
	if (!board.GetBaseAddress()) return;

	// 等波次数据就绪（WaveCount > 0）
	if (board.WaveCount <= 0) return;

	g_waveConfigPending = false;

	// 导出模式
	{
		std::ifstream flagFile("waves_export.flag");
		if (flagFile.is_open())
		{
			flagFile.close();
			InitZombieNameMap();
			ExportCurrentLevelWaves("waves_exported.ini", boardAddress);
			return;
		}
	}

	// 配置模式
	std::string levelKey = MakeLevelKey(board);
	PVZ::PVZApp app = board.GetPVZApp();
	LevelWaveConfig* pCfg = nullptr;

	if (app.GetBaseAddress() && app.LevelId == PVZLevel::Adventure)
	{
		PVZ::SaveData sd = PVZ::GetSaveData();
		if (sd.GetBaseAddress() && sd.AdventureFinishCount >= 1)
		{
			std::string key2nd = "Adventure2:" + levelKey.substr(levelKey.find(':') + 1);
			auto it2 = g_waveConfigs.find(key2nd);
			if (it2 != g_waveConfigs.end())
				pCfg = &(it2->second);
		}
	}

	if (!pCfg)
	{
		auto it = g_waveConfigs.find(levelKey);
		if (it != g_waveConfigs.end())
			pCfg = &(it->second);
	}

	if (!pCfg)
		return;

	LevelWaveConfig& cfg = *pCfg;

	// 1. 旗帜数（直接写 0x5564 总波数字段）
	// ★ 不能走 PVZ.h 的 board.WaveCount setter：它实现的是"当前波推进"语义
	//   （value <= WaveCount 只允许改小 + 写 0x5610 进度条 = value*150/WaveCount），
	//   初始化总波数会被"只能改小"拒绝（应用时机碰上游 WaveCount 中间态时波数
	//   设置失败 → 只剩默认 1 波、永不重试）且把进度条直接拉满。
	if (cfg.waveCount > 0)
	{
		MemSafeWrite<int>(boardAddress + 0x5564, cfg.waveCount);
		// 进度条复位：旧版 setter 曾把 0x5610 写成 150（满格），而游戏进度条
		// 只递增不递减 → 一旦污染永不恢复，进关时强制归零（游戏按 CurrentWave 重算）
		MemSafeWrite<int>(boardAddress + 0x5610, 0);
		int wcAfter = MemSafeRead<int>(boardAddress + 0x5564);
		// 防御：极端情况写入失败时放弃本次应用（直接写内存通常必成功）
		if (wcAfter != cfg.waveCount)
			return;
	}

	// 2. 出怪种类
	std::set<ZombieType::ZombieType> allTypes;
	for (auto& wp : cfg.waves)
		for (auto& zt : wp.second.zombies)
		{
			// 自定义僵尸在游戏内按基础类型出怪：撑杆司令(33)→撑杆僵尸(3)、
			// 防爆门(34)→铁门僵尸(6)。允许标志区(33字节)只能写0~32
			ZombieType::ZombieType t = zt;
			if (zt == ZombieType::PoleCommanderZombie)
				t = ZombieType::PoleVaultingZombie;
			else if (zt == ZombieType::BlastproofDoorZombie)
				t = ZombieType::ScreenDoorZombie;
			allTypes.insert(t);
		}

	if (!allTypes.empty())
	{
		ZombieType::ZombieType ta[33];
		int idx = 0;
		for (auto& zt : allTypes) ta[idx++] = zt;
		SetZombieAllowedDirect(boardAddress, ta, idx);
	}

	// 3. 逐波设置（自定义僵尸槽位 → 基础类型 + 记录槽位序号）
	// ★ 语义必须一致：标记时用的是"本波第几个基础类型"（MarkPoleCommander 的
	//   g_type3SeenInWave / MarkBlastproofDoor 的 g_type6SeenInWave），所以这里记录的
	//   是"该槽位是本波第几只类型3/类型6"，而不是波内绝对槽位号（波里混着普通僵尸时
	//   两者不同！实测 Wave3=[Zombie,Zombie,Conehead,PoleCommander] 司令在绝对槽位3
	//   但类型3序号是0，用绝对槽位记录会导致永远匹配不上）
	g_commanderWaveSlots.clear();
	g_blastWaveSlots.clear();
	for (auto& wp : cfg.waves)
	{
		if (wp.first >= 0 && wp.first < board.WaveCount)
		{
			PVZ::Wave w = board.GetWave(wp.first);
			if (!w.GetBaseAddress())
				continue;

			// 转写后的出怪列表 + 本波司令"类型3序号"集合 + 本波防爆门"类型6序号"集合
			std::vector<ZombieType::ZombieType> finalList;
			std::set<int> cmdSlots;
			std::set<int> blastSlots;
			int type3Idx = 0; // 本波第几个类型3（转写后仍是类型3的都计数）
			int type6Idx = 0; // 本波第几个类型6（转写后仍是类型6的都计数）
			for (auto& zt : wp.second.zombies)
			{
				if (zt == ZombieType::PoleCommanderZombie)
				{
					finalList.push_back(ZombieType::PoleVaultingZombie);
					cmdSlots.insert(type3Idx); // 记录"第几个类型3"
				}
				else if (zt == ZombieType::BlastproofDoorZombie)
				{
					finalList.push_back(ZombieType::ScreenDoorZombie);
					blastSlots.insert(type6Idx); // 记录"第几个类型6"
				}
				else
				{
					finalList.push_back(zt);
				}
				if (zt == ZombieType::PoleVaultingZombie || zt == ZombieType::PoleCommanderZombie)
					type3Idx++;
				if (zt == ZombieType::ScreenDoorZombie || zt == ZombieType::BlastproofDoorZombie)
					type6Idx++;
			}
			if (!cmdSlots.empty())
				g_commanderWaveSlots[wp.first] = cmdSlots;
			if (!blastSlots.empty())
				g_blastWaveSlots[wp.first] = blastSlots;

			w.SetAll(finalList.data(), finalList.size());
		}
	}
}

// ==================== 寒冰射手冰锥贴图替换 ====================
// 由 ProjectileImageEvent 调用，在游戏绘制子弹时替换冰锥图片
extern "C" __declspec(dllexport) int GetProjectileImage(DWORD projectileAddress, int imgParam)
{
	// imgParam == 0: PROJECTILE_IMAGEROW（行号）→ 使用默认
	// imgParam == 1: PROJECTILE_IMAGE（图片基址）→ 替换为冰锥贴图
	if (imgParam == 1 && g_icicleImageAddr != 0)
	{
		auto it = g_snowPeaIcicleProjectiles.find(projectileAddress);
		if (it != g_snowPeaIcicleProjectiles.end())
			return (int)g_icicleImageAddr;
	}
	return -1; // 返回-1使用默认值
}



// ============================================================================
// 墓碑吞噬者（GraveBuster, SeedType=11）等阶机制：实现
// ============================================================================
// 全局状态/配置声明见文件前部"墓碑吞噬者配置"段；本段只放实现。
//
// 触发链路（零 hook）：
//   GbFrame 每帧
//     ① 刷新 armed 表（本格种过墓碑吞噬者 → 记 (row,col,tier) + hold 计数）
//     ② 扫 Board::GetAllGriditems<Grave>() 得到本帧墓碑集合
//     ③ 与上一帧比对：上一帧有、本帧没有 ⇒ 该格墓碑消失
//     ④ 若该格 armed 命中 ⇒ GbReward() 按 tier 结算
//     ⑤ 经验包掉落物做抛物线物理 + 到期清理
//   ★ 依据 Plant::UpdateGraveBuster @0x45FC70（中文版反汇编实证）：
//     State==9 && [+0x54]==0 → call 0x408E40 取墓碑 → call 0x44D000 移除 → 0x4679B0 Kill。
//     所以"墓碑消失"这一刻植物已经被判定死亡，产出物一律以【格坐标】定位，不锚植物。
//
// 铁律遵守：
//   · 本段全部跑在轮询帧（onGameObjectsUpdate），允许 std::vector / 文件 IO；
//   · 但不在函数内直接写 __try（含 C++ 对象展开会触发 MSVC C2712）→ 需要 __try 的
//     小动作拆到独立函数（GbLoadPackImage / GbTryCreatePlantCard / DrawGbUI）。
//   · 图片加载失败只尝试一次（项目踩过"每帧重试 → 每帧泄漏 → 堆耗尽"的坑）。

static DWORD g_gbPackImg      = 0;      // 经验包图标（images\Fertilizer.png）
static bool  g_gbPackImgTried = false;  // 只尝试加载一次
static bool  g_gbDbgCardsLogged = false;// GB_DEBUG：本关是否已落盘卡槽探针
static int   g_gbRngState     = 0x2F6E2B1;

static int GbRand(int n)
{
	if (n <= 1)
		return 0;
	g_gbRngState = g_gbRngState * 1103515245 + 12345;
	int v = (g_gbRngState >> 16) & 0x7FFF;
	return v % n;
}

static bool GbSeedExcluded(int seedType)
{
	for (int i = 0; i < g_gbExcludeCount; i++)
		if (g_gbExcludeSeeds[i] == seedType)
			return true;
	return false;
}

// ---- 卡片级永久经验存档（跨关卡，工作目录 grave_buster_card.dat）----
static const char* GB_CARD_SAVE_FILE = "grave_buster_card.dat";

static void GbCardExpLoad()
{
	if (g_gbCardExpLoaded)
		return;
	g_gbCardExpLoaded = true;
	std::ifstream f(GB_CARD_SAVE_FILE);
	if (!f.is_open())
		return;
	int v = 0;
	if (f >> v)
	{
		if (v < 0) v = 0;
		if (v > 1000000) v = 1000000;
		g_gbCardExp = v;
	}
	f.close();
}

static void GbCardExpSave(int v)
{
	std::ofstream f(GB_CARD_SAVE_FILE, std::ios::trunc);
	if (!f.is_open())
		return;
	f << v << "\n";
	f.close();
}

// ---- 经验包图标（只在轮询帧加载；失败永久跳过）----
static void GbLoadPackImage()
{
	__try
	{
		DWORD isNew = 0;
		Draw::PString fn = Draw::ToString("images\\Fertilizer.png");
		Draw::PString variant = Draw::ToString("");
		DWORD ref = Draw::GetSharedImage(isNew, variant, fn);
		if (ref != 0)
			g_gbPackImg = Draw::SharedImageRefToImage(ref);
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		g_gbPackImg = 0;
	}
}

// ---- armed 表（该格种过墓碑吞噬者）----
static GbArmRec* GbFindArmByPlant(DWORD plant)
{
	for (int i = 0; i < g_gbArmCount; i++)
		if (g_gbArms[i].plant == (int)plant)
			return &g_gbArms[i];
	return 0;
}

static GbArmRec* GbFindArmByCell(int row, int col)
{
	for (int i = 0; i < g_gbArmCount; i++)
		if (g_gbArms[i].hold > 0 && g_gbArms[i].row == row && g_gbArms[i].col == col)
			return &g_gbArms[i];
	return 0;
}

static void GbRemoveArm(int idx)
{
	if (idx < 0 || idx >= g_gbArmCount)
		return;
	for (int i = idx; i < g_gbArmCount - 1; i++)
		g_gbArms[i] = g_gbArms[i + 1];
	g_gbArmCount--;
}

// ---- 经验包掉落物 ----
static bool GbItemCenter(int idx, int* outCx, int* outCy)
{
	if (idx < 0 || idx >= g_gbItemCount)
		return false;
	if (!g_gbItems[idx].alive)
		return false;
	int bob = g_gbItems[idx].settled
		? (int)(sinf((float)(MgPlayingTime() - g_gbItems[idx].spawnCs) * 0.06f) * 3.0f)
		: 0;
	*outCx = (int)g_gbItems[idx].x;
	*outCy = (int)g_gbItems[idx].y + bob;
	return true;
}

static void GbCompactItems()
{
	int w = 0;
	int newSelected = -1;
	for (int i = 0; i < g_gbItemCount; i++)
	{
		if (!g_gbItems[i].alive)
		{
			if (g_gbSelected == i)
				g_gbSelected = -1;
			continue;
		}
		if (g_gbSelected == i)
			newSelected = w;
		g_gbItems[w++] = g_gbItems[i];
	}
	g_gbItemCount = w;
	g_gbSelected = newSelected;
}

// 产出一个"跳出"的经验包（从墓碑位置向上抛，落地弹两下）
static void GbSpawnItem(DWORD boardAddr, int row, int col)
{
	if (g_gbItemCount >= GB_MAX_ITEMS)
		return;
	PVZ::Board bd(boardAddr);
	if (!bd.GetBaseAddress())
		return;
	int gx = bd.GridToXPixel(row, col);
	int gy = bd.GridToYPixel(row, col);
	// 动画速度倍率：整体时间 ×(1/spd)。抛物线保持同样高度/落点 ⇒ v×spd、g×spd²。
	float spd = g_gbItemAnimSpeed;
	if (spd < 0.2f) spd = 0.2f;
	if (spd > 3.0f) spd = 3.0f;
	GbItemRec& it = g_gbItems[g_gbItemCount++];
	it.x        = (float)(gx + 40);
	it.y        = (float)(gy + 52);   // 墓碑底部起跳
	it.vy       = -8.0f * spd;        // 初速向上 ≈ 51px 弹高 → "跳出来"（0.8 倍速 ≈ -6.4）
	it.groundY  = gy + 58;            // 落点（土面）
	it.bounces  = 0;
	it.settled  = 0;
	it.alive    = 1;
	it.spawnCs  = bd.PlayingTime;
}

static void GbUpdateItemPhysics()
{
	int now = MgPlayingTime();
	// 动画速度倍率（同 GbSpawnItem）：抛物线 y(t)=y0+v0t+½gt² 整体慢 spd 倍 ⇒ g×spd²，
	// 反弹阈值同比例缩小，保证 0.8 倍速下仍然是"弹两下"而不是提前停住。
	float spd = g_gbItemAnimSpeed;
	if (spd < 0.2f) spd = 0.2f;
	if (spd > 3.0f) spd = 3.0f;
	float grav      = 0.62f * spd * spd;
	float bounceThr = 2.0f * spd;
	for (int i = 0; i < g_gbItemCount; i++)
	{
		GbItemRec& it = g_gbItems[i];
		if (!it.alive)
			continue;
		if (now - it.spawnCs > g_gbItemLifeCs && g_gbSelected != i)
		{
			it.alive = 0;           // 到期消失（选中中的不消失）
			continue;
		}
		if (it.settled)
			continue;
		it.vy += grav;              // 重力
		it.y  += it.vy;
		if (it.y >= (float)it.groundY)
		{
			it.y = (float)it.groundY;
			if (it.bounces < 2 && it.vy > bounceThr)
			{
				it.vy = -it.vy * 0.38f;   // 衰减反弹
				it.bounces++;
			}
			else
			{
				it.vy = 0.0f;
				it.settled = 1;
			}
		}
	}
	GbCompactItems();
}

// ---- 1 阶：该植物卡剩余冷却减半 ----
// SeedCard 字段（PVZ.h / Classes/SeedCard.cpp 实证）：
//   +0x24 CoolDown（已冷却时间，从 0 长到 +0x28）、+0x28 CoolDownInterval、
//   +0x34 ContentCard、+0x38 ContentCardImitative、+0x49 Active（是否冷却中）
static void GbRefundCooldown(DWORD boardAddr)
{
	PVZ::Board bd(boardAddr);
	PVZ::CardSlot slot = bd.GetCardSlot();
	DWORD sb = (DWORD)slot.GetBaseAddress();
	if (sb < 0x10000)
		return;
	for (int i = 0; i < 10; i++)
	{
		DWORD card = sb + 0x28 + (DWORD)i * 0x50;
		int type = MemSafeRead<int>(card + 0x34);
		bool isTarget = (type == (int)SeedType::GraveBuster);
		if (!isTarget && type == (int)SeedType::Imitater)
		{
			// 模仿者卡：实际植物在 +0x38
			if (MemSafeRead<int>(card + 0x38) == (int)SeedType::GraveBuster)
				isTarget = true;
		}
		if (!isTarget)
			continue;
		BYTE active = MemSafeRead<BYTE>(card + 0x49);
		int  cd     = MemSafeRead<int>(card + 0x24);
		int  iv     = MemSafeRead<int>(card + 0x28);
		// 合理性校验：中文版偏移若不符则这里是垃圾值 → 直接跳过，绝不乱写
		if (!active || iv <= 0 || iv > 100000 || cd < 0 || cd >= iv)
			continue;
		int remain = iv - cd;
		MemSafeWrite<int>(card + 0x24, cd + remain / 2);
	}
}

// ---- 2 阶：原地等概率生成 普通/路障/铁桶/橄榄 ----
// ---- 2 阶：原地等概率生成"被魅惑"的 普通/路障/铁桶/橄榄 ----
// ★ 用户 2026-10-22 修正：是「魅惑僵尸」不是普通僵尸 —— 生成后立刻走原版魅惑
//   （PVZ::Zombie::Hypnotize() = 0x52FA60 StartMindControlled，与魅惑菇2阶额外普僵同一通道，
//     眼睛发紫 + 掉头打自己人，全套视觉/索敌由原版处理）。
static void GbSpawnRandomZombie(int row, int col)
{
	if (g_gbZombieTypeCount <= 0)
		return;
	int idx = GbRand(g_gbZombieTypeCount);
	int zt  = g_gbZombieTypes[idx];
	if (zt < 0)
		return;
	PVZ::Zombie nz = Creator::CreateZombie((ZombieType::ZombieType)zt, row, (byte)col);
	if (nz.GetBaseAddress() < 0x10000)
		return;
	nz.Hypnotize();
}

// ---- 3 阶：从本关卡槽随机一张植物卡，用原版 Coin(PlantCard) 跳出 ----
// 原版依据：Challenge 开罐出卡 @0x429B9E
//   push 2(motion=Product) / push 0x10(type=PlantCard) / push y / push x
//   call 0x40CB10 → mov ecx,[vase+0x40]; mov [eax+0x68],ecx  （+0x68 = ContentCard）
static bool GbTryCreatePlantCard(DWORD boardAddr, int row, int col, int seedType)
{
	__try
	{
		PVZ::Board bd(boardAddr);
		int gx = bd.GridToXPixel(row, col);
		int gy = bd.GridToYPixel(row, col);
		PVZ::Coin coin = Creator::CreateCoin(CoinType::PlantCard, gx + 20, gy, CoinMotionType::Product);
		DWORD ca = (DWORD)coin.GetBaseAddress();
		if (ca < 0x10000)
			return false;
		MemSafeWrite<int>(ca + 0x68, seedType);
		return true;
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
		return false;
	}
}

static void GbSpawnPlantCard(DWORD boardAddr, int row, int col)
{
	PVZ::Board bd(boardAddr);
	PVZ::CardSlot slot = bd.GetCardSlot();
	DWORD sb = (DWORD)slot.GetBaseAddress();
	if (sb < 0x10000)
		return;
	int cand[12];
	int n = 0;
	for (int i = 0; i < 10; i++)
	{
		DWORD card = sb + 0x28 + (DWORD)i * 0x50;
		int type = MemSafeRead<int>(card + 0x34);
		if (type == (int)SeedType::Imitater)
			type = MemSafeRead<int>(card + 0x38);   // 模仿者 → 实际植物
		if (type < 0 || type > 47)
			continue;
		if (GbSeedExcluded(type))
			continue;
		cand[n++] = type;
	}
	if (n <= 0)
		return;
	int pick = cand[GbRand(n)];
	GbTryCreatePlantCard(boardAddr, row, col, pick);
}

// ---- 结算：按等阶发奖（0/1/2/3 逐级叠加，"除以上外"）----
static void GbReward(DWORD boardAddr, int row, int col, int tier)
{
	if (tier < 0)
		tier = 0;
	if (tier > 3)
		tier = 3;
	GbSpawnItem(boardAddr, row, col);                 // 0 阶起：经验包
	// 可选加速（GB_DIG_EXP>0 才生效，默认 0 = 严格按用户定案"只靠肥料/队友分经验"）：
	// 每次吞噬成功直接给卡片一笔经验 —— 因为墓碑吞噬者存活仅约 4 秒，
	// 单靠肥料冷却 7.5s / 队友分经验，实战中几乎喂不到 2/3 阶。
	if (g_gbDigExp > 0)
	{
		g_gbCardExp += g_gbDigExp;
		int lim = GetSeedExperienceLimit((int)SeedType::GraveBuster);
		if (lim > 0 && g_gbCardExp > lim)
			g_gbCardExp = lim;
		g_gbCardSavePending = g_gbCardExp;
	}
	if (tier >= 1)
		GbRefundCooldown(boardAddr);                  // 1 阶：冷却减半
	if (tier >= 2)
		GbSpawnRandomZombie(row, col);                // 2 阶：随机僵尸
	if (tier >= 3)
		GbSpawnPlantCard(boardAddr, row, col);        // 3 阶：随机植物卡
}

// ---- 主轮询 ----
static void GbFrame(DWORD boardAddress)
{
	if (!CrashIsReadable(boardAddress, 0x100))
		return;
	if (!g_gbCardExpLoaded)
		GbCardExpLoad();
	if (!g_gbPackImgTried)
	{
		g_gbPackImgTried = true;
		GbLoadPackImage();
	}
	// 卡片经验回写（onPlantRemove 注册的待落盘值）
	if (g_gbCardSavePending >= 0)
	{
		g_gbCardExp = g_gbCardSavePending;
		g_gbCardSavePending = -1;
		GbCardExpSave(g_gbCardExp);
	}

	GbUpdateItemPhysics();

	PVZ::Board board(boardAddress);
	if (!board.GetBaseAddress())
		return;
	int now = board.PlayingTime;

	// 排障探针（GB_DEBUG=1，每关一次）：把 seedbank 指针与各卡槽字段落盘，
	// 用于确认中文版 Board+0x144 / SeedCard 偏移是否如框架所述（1阶冷却返还依赖它）
	if (g_gbDebug && !g_gbDbgCardsLogged)
	{
		g_gbDbgCardsLogged = true;
		PVZ::CardSlot slot = board.GetCardSlot();
		DWORD sb = (DWORD)slot.GetBaseAddress();
		CrashLineHex("[GB] seedbank", sb);
		if (sb >= 0x10000)
		{
			for (int i = 0; i < 10; i++)
			{
				DWORD card = sb + 0x28 + (DWORD)i * 0x50;
				CrashLineHex("[GB] card.type", (DWORD)MemSafeRead<int>(card + 0x34));
				CrashLineHex("[GB] card.cd",   (DWORD)MemSafeRead<int>(card + 0x24));
				CrashLineHex("[GB] card.iv",   (DWORD)MemSafeRead<int>(card + 0x28));
			}
		}
	}

	// ① armed 衰减（植物消失后 hold 递减）
	for (int i = 0; i < g_gbArmCount; i++)
	{
		if (g_gbArms[i].hold > 0)
			g_gbArms[i].hold--;
	}
	// ② 存活墓碑吞噬者 → 刷新/新增 armed
	auto plants = board.GetAllPlants();
	for (auto& plant : plants)
	{
		if (plant.NotExist)
			continue;
		if (plant.Type != SeedType::GraveBuster)
			continue;
		DWORD addr = (DWORD)plant.GetBaseAddress();
		if (addr < 0x10000)
			continue;
		int row = (int)plant.Row;
		int col = (int)plant.Column;
		if (row < 0 || row > 5 || col < 0 || col > 8)
			continue;
		int exp = 0;
		auto it = g_plantExperience.find(addr);
		if (it != g_plantExperience.end())
			exp = it->second;
		int tier = GetPlantTier((int)SeedType::GraveBuster, exp);
		GbArmRec* rec = GbFindArmByPlant(addr);
		if (!rec)
		{
			if (g_gbArmCount >= GB_MAX_ARMS)
				continue;
			rec = &g_gbArms[g_gbArmCount++];
			rec->plant = (int)addr;
		}
		rec->row  = row;
		rec->col  = col;
		rec->tier = tier;
		rec->hold = GB_ARM_HOLD;
	}
	// ③ 清掉到期记录
	for (int i = g_gbArmCount - 1; i >= 0; i--)
	{
		if (g_gbArms[i].hold <= 0)
			GbRemoveArm(i);
	}

	// ④ 本帧墓碑集合
	GbGraveKey cur[GB_MAX_GRAVES];
	int curCount = 0;
	auto graves = board.GetAllGriditems<PVZ::Grave>();
	for (auto& gv : graves)
	{
		if (curCount >= GB_MAX_GRAVES)
			break;
		if (gv.NotExist)
			continue;
		int r = (int)gv.Row;
		int c = (int)gv.Column;
		if (r < 0 || r > 5 || c < 0 || c > 8)
			continue;
		cur[curCount].row = r;
		cur[curCount].col = c;
		curCount++;
	}
	// ⑤ 与上一帧比对：消失的墓碑 = 被吞噬
	for (int i = 0; i < g_gbPrevGraveCount; i++)
	{
		int pr = g_gbPrevGraves[i].row;
		int pc = g_gbPrevGraves[i].col;
		bool stillThere = false;
		for (int k = 0; k < curCount; k++)
		{
			if (cur[k].row == pr && cur[k].col == pc)
			{
				stillThere = true;
				break;
			}
		}
		if (stillThere)
			continue;
		GbArmRec* arm = GbFindArmByCell(pr, pc);
		if (!arm)
			continue;                 // 该格没种过墓碑吞噬者 → 不是它挖的
		int tier = arm->tier;
		arm->hold = 0;                // 消耗（防重复结算）
		GbReward(boardAddress, pr, pc, tier);
		if (g_gbDebug)
			CrashLineHex("[GB] eaten tier", (DWORD)tier);
	}
	// ⑥ 保存本帧快照
	g_gbPrevGraveCount = curCount;
	for (int i = 0; i < curCount; i++)
		g_gbPrevGraves[i] = cur[i];
	(void)now;
}

static void GbResetAll()
{
	g_gbArmCount        = 0;
	g_gbPrevGraveCount  = 0;
	g_gbItemCount       = 0;
	g_gbSelected        = -1;
	g_gbDbgCardsLogged  = false;
	memset(g_gbArms, 0, sizeof(g_gbArms));
	memset(g_gbItems, 0, sizeof(g_gbItems));
}

// ---- 绘制（onDrawUITop）----
static void DrawGbUI()
{
	DWORD g = (g_expPouchGStore != 0) ? MemSafeRead<DWORD>(g_expPouchGStore) : 0;
	if (!g || !ExpPouchGraphicsValid(g))
		return;
	__try
	{
		for (int i = 0; i < g_gbItemCount; i++)
		{
			if (!g_gbItems[i].alive || g_gbSelected == i)
				continue;
			int cx = 0, cy = 0;
			if (!GbItemCenter(i, &cx, &cy))
				continue;
			if (g_gbPackImg)
				Draw::DrawImage(cx - 40, cy - 40, g_gbPackImg, g);
		}
		// 选中的跟随鼠标（同金盏花/经验包范式）
		if (g_gbSelected >= 0 && g_gbSelected < g_gbItemCount
			&& g_expPouchMouseX >= 0 && g_expPouchMouseY >= 0 && g_gbPackImg)
		{
			Draw::DrawImage(g_expPouchMouseX - 40, g_expPouchMouseY - 40, g_gbPackImg, g);
		}
	}
	__except (EXCEPTION_EXECUTE_HANDLER)
	{
	}
}

// ---- 鼠标交互（Board::MouseDown，由 HandleExpPouchMouseDown 调用）----
// 流程与金盏花产出物完全一致：单击拾起 → 拖动 → 单击目标植物生效 / 点空地取消
static int GbHandleMouseDown(DWORD boardAddr, int x, int y)
{
	// 1) 已拾起：点目标植物生效；点自己/空地取消
	if (g_gbSelected >= 0)
	{
		int cx = 0, cy = 0;
		if (GbItemCenter(g_gbSelected, &cx, &cy)
			&& x >= cx - 26 && x <= cx + 26 && y >= cy - 26 && y <= cy + 26)
		{
			g_gbSelected = -1;
			return 1;
		}
		int col = -1, row = -1;
		if (ExpPouchPixelToGrid(boardAddr, x, y, &col, &row))
		{
			DWORD target = ExpPouchFindPlantAt(boardAddr, row, col);
			if (target)
			{
				AddPlantExperience(target, g_gbExpPackGain);
				// 施肥动画（复用金盏花肥料同款 reanim + 音效）
				int tpx = MemSafeRead<int>(target + 0x8);
				int tpy = MemSafeRead<int>(target + 0xC);
				int tpw = MemSafeRead<int>(target + 0x10);
				int tph = MemSafeRead<int>(target + 0x14);
				int tlayer = MemSafeRead<int>(target + 0x20);
				if (tpw > 0 && tpw <= 400 && tph > 0 && tph <= 400)
					MgPlayUseAnim(0, tpx + tpw / 2, tpy + tph / 2, tlayer);
				MgPlayUseSound(0);
				if (g_gbSelected >= 0 && g_gbSelected < g_gbItemCount)
					g_gbItems[g_gbSelected].alive = 0;
				g_gbSelected = -1;
				GbCompactItems();
				return 1;
			}
		}
		g_gbSelected = -1;   // 点空地：取消拾起（经验包保留）
		return 1;
	}
	// 2) 未拾起：点到经验包 → 拾起
	for (int i = 0; i < g_gbItemCount; i++)
	{
		int cx = 0, cy = 0;
		if (!GbItemCenter(i, &cx, &cy))
			continue;
		if (x >= cx - 26 && x <= cx + 26 && y >= cy - 26 && y <= cy + 26)
		{
			g_gbSelected = i;
			g_expPouchSelected = false;   // 与右上角经验包互斥
			g_mgSelected = -1;            // 与金盏花产出物互斥
			return 1;
		}
	}
	return 0;
}
