# PVZ 飞升版 / PVZ Ascension

一个基于 [PVZClass](https://github.com/PVZClasses/pvzclass) 框架的《植物大战僵尸》
（1.0.0.1051 版本）改版，核心是给植物加了**六阶经验成长系统**，
并围绕等阶重做了大量植物的攻击与行为机制。

本仓库只包含**改版自己的 DLL 源码与配置文件**，不含游戏本体、不含游戏素材、
不含 PVZClass 框架源码。

---

## 免责声明

- 本项目是**非官方的爱好者改版**，与 Electronic Arts Inc. / PopCap Games
  没有任何关联，未获其授权或认可。
- 本仓库**不包含**任何游戏原始文件（程序、贴图、动画、音频等）。
  使用本项目需要你**自行拥有正版《植物大战僵尸》1.0.0.1051**。
- 本项目不提供游戏下载，也不包含任何来自其他改版的素材。
- 因使用本项目产生的任何后果由使用者自行承担。

---

## 功能概览

**六阶经验系统**

- 每株植物独立累计经验，从 `Lv.0` 成长到 `Lv.5`
- 击杀僵尸获得经验；使用肥料（100 阳光）可直接换取 300 点经验
- 等阶影响攻击速度、伤害、血量、投射物形态等，具体数值全部外置到 `.ini`
- 部分植物在特定等阶解锁额外机制（例如多重投掷、穿透、链击、克隆、范围爆发等）

**其他**

- 击杀/种植事件驱动的 UI 绘制：植物头顶显示等阶与经验进度
- 僵尸侧改动：部分僵尸重新设定血量与行为（如撑杆司令）
- 所有可调数值集中在 7 个 `.ini` 文件里，改文本即可，无需重新编译

---

## 目录结构

```
.
├── build.bat                  一键构建脚本（Release | Win32）
├── pvzclass.sln               解决方案（pvzclass + pvzdll）
├── pvzdll/                    ← 本项目的全部源码
│   ├── pch.cpp                主实现（约 2.2 万行）
│   ├── pch.h                  DLL 导出的事件入口声明
│   ├── dllmain.cpp            DllMain
│   ├── framework.h
│   ├── assets/                经验值数字字形位图（绘制用）
│   ├── plant_tier.ini         等阶阈值与经验曲线
│   ├── plant_attack_speed.ini 各等阶攻击间隔
│   ├── plant_mechanics.ini    各植物的机制参数
│   ├── plant_cost.ini         种植阳光消耗
│   ├── plant_unlock.ini       解锁条件
│   ├── zombie_mechanics.ini   僵尸血量/速度
│   └── waves.ini              波次配置
└── pvzclass/                  ← 不放仓库，需自行放入框架（见下）
```

---

## 构建

**环境要求**

| 项目 | 要求 |
|---|---|
| 操作系统 | Windows |
| 编译器 | Visual Studio 2019 (v142) 或 2022 (v143)，含「使用 C++ 的桌面开发」 |
| 平台 | **Win32 / x86**（必须 32 位，游戏是 32 位进程） |
| 配置 | Release |
| 游戏 | 植物大战僵尸 **1.0.0.1051** |

**步骤**

1. 克隆本仓库

   ```bat
   git clone https://github.com/<your-name>/PVZ-Ascension.git
   cd PVZ-Ascension
   ```

2. 获取 PVZClass 框架，放到 `.\pvzclass\`

   从 https://github.com/PVZClasses/pvzclass 下载后解压，
   使下面这个文件存在：

   ```
   PVZ-Ascension\pvzclass\pvzclass.vcxproj
   ```

3. 构建

   ```bat
   build.bat
   ```

   产物：`Release\pvzdll.dll`

4. （可选）构建并部署到游戏目录

   ```bat
   build.bat "D:\Games\PlantsVsZombies"
   ```

   脚本会复制 `pvzdll.dll`、缺失的 `.ini`、以及 `assets\expfontcoin14\*.png`。
   **已存在的 `.ini` 不会被覆盖**，你的自定义参数会保留。

5. 运行

   先启动游戏到主菜单，再运行框架编译出的注入器 `pvzmain.exe`。
   没有注入器时 DLL 虽然能加载，但事件不会触发，UI 也不会出现。

> 如果 `build.bat` 找不到 Visual Studio，打开脚本把 `VS_MANUAL`
> 设成你的 VS 安装目录即可，例如
> `set "VS_MANUAL=D:\Microsoft Visual Studio\2022\Community"`。

---

## 配置

所有数值都在 `pvzdll/*.ini` 里，格式是 `键 = 值`。

| 文件 | 作用 |
|---|---|
| `plant_tier.ini` | 每阶所需经验、等级上限、各植物是否启用等阶 |
| `plant_attack_speed.ini` | 每株植物各等阶的攻击间隔（秒） |
| `plant_mechanics.ini` | 各植物的机制开关与数值（伤害、范围、概率、冷却…） |
| `plant_cost.ini` | 种植阳光消耗 |
| `plant_unlock.ini` | 植物解锁条件 |
| `zombie_mechanics.ini` | 僵尸血量、移速倍率 |
| `waves.ini` | 波次构成与节奏 |

改完直接覆盖到游戏目录即可生效，不需要重新编译。

---

## 调试日志（给开发者）

源码里保留了 10 个硬编码的诊断日志路径，全部写向 `D:\` 根目录。它们是开发期
定位崩溃用的，**正常运行不需要它们**：

| 路径 | 用途 |
|---|---|
| `D:\pvz_crash.log` | 崩溃上下文：模块表 + 崩溃地址 + 关键对象状态 |
| `D:\pvz_expsave.log` | 经验值存取与等阶提升记录 |
| `D:\pvz_plantcfg_debug.log` | 植物配置（ini）加载结果 |
| `D:\pvz_ice_debug.log` | 寒冰系植物/子弹诊断 |
| `D:\pvz_fume_debug.log` | 大喷菇气浪范围诊断 |
| `D:\pvz_garlic.log` | 大蒜位移与换行诊断 |
| `D:\pvz_split_debug.log` | 分裂弹（散射）诊断 |
| `D:\pvz_fireball_tbl.txt` | 火球类型表 dump |
| `D:\pvz_flash_diag.txt` | 绘制闪烁诊断 |
| `D:\pvz_ulf_debug.txt` | UI 层绘制顺序诊断 |

几点说明：

- 写入失败是**静默忽略**的（`fopen` 返回空即跳过），没有 D 盘也不会崩溃或弹窗
- 这些是普通文本文件，不占空间，可以随时删除
- 想彻底关掉：在 `pch.cpp` 里搜索 `fopen("D:\\pvz_`，把对应行注释掉即可，
  不影响机制逻辑
- 反馈 bug 时附上 `pvz_crash.log` 会有很大帮助

---

## 已知问题

- `pch.cpp` 是单文件实现，体积较大。这是历史原因（早期迭代为了方便热改），
  拆分重构尚未进行。
- 仅适配 **1.0.0.1051**。其他版本的游戏内存布局不同，会崩溃。

## 构建失败排查

**`error MSB6001: "CL.exe"的命令行开关无效 / 已添加项。字典中的关键字:"HTTPS_PROXY"`**

Windows 环境变量不区分大小写，如果你的系统里同时存在 `HTTPS_PROXY` 和
`https_proxy` 两个变量（常见于一键代理脚本、Clash、v2rayN 等工具），
MSBuild 在构造子进程环境时会直接抛异常。

在运行 `build.bat` 的 cmd 窗口里先清掉其中一套即可：

```bat
set HTTPS_PROXY=
set HTTP_PROXY=
build.bat
```

**`[ERROR] Could not locate Visual Studio automatically`**

打开 `build.bat`，把 `VS_MANUAL` 改成你的 VS 安装目录：

```bat
set "VS_MANUAL=D:\Microsoft Visual Studio\2022\Community"
```

**编译成功但进游戏没反应**

绝大多数情况是没跑注入器。DLL 只是被游戏进程加载，事件钩子由框架编译出的
`pvzmain.exe` 完成注册——必须先启动游戏，再运行 `pvzmain.exe`。


---

## 许可证

本项目自有源码（`pvzdll/` 下的全部文件）以 **MIT** 协议发布：

> 你可以自由使用、复制、修改、合并、发布、分发、再授权、销售本软件，
> 包括商业用途和闭源分发。
> 唯一的要求是：在所有副本或软件的实质部分中，保留上面的版权声明与本许可声明。

完整文本见 [`LICENSE`](LICENSE)。

**关于编译产物**：`pvzdll.dll` 链接了同样使用 MIT 协议的 PVZClass 框架，
分发 DLL 时请一并保留框架的版权声明。详见
[`THIRD-PARTY-NOTICES.md`](THIRD-PARTY-NOTICES.md)。

游戏本体的版权归 EA / PopCap 所有，不在本许可证覆盖范围内。

---

## 关于 AI 辅助开发

本项目的绝大部分代码是在 AI 辅助下完成的：作者负责玩法设计、机制规格、
逆向地址定位、实机调试与问题诊断，AI 负责代码生成与重构。

这些代码按上面的 MIT 协议发布——不论你是否认可 AI 生成部分的版权归属，
你都可以按 MIT 的条款自由使用它。

---

## 致谢

- [PVZClasses/pvzclass](https://github.com/PVZClasses/pvzclass) —— 没有这个框架就没有本项目
- 植物大战僵尸改版社区中分享逆向资料与思路的各位
