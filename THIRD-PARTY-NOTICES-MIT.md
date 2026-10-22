# 第三方组件声明 / Third-Party Notices

本仓库的**自有源码**（`pvzdll/` 目录下的全部文件）以 **MIT** 协议发布，
见根目录 `LICENSE`。

本仓库**不包含**任何游戏原始素材，也不包含 PVZClass 框架的源码。
但编译产物（`pvzdll.dll`）在构建过程中会链接 PVZClass 框架，
因此**分发的 DLL 二进制**中包含该框架的目标代码，须遵守其 MIT 协议。

---

## 1. PVZClass 框架

- 项目主页：https://github.com/PVZClasses/pvzclass
- 许可证：MIT License
- 版权：Copyright (c) 2025 PVZClasses
- 用途：本项目通过其头文件与静态库（`pvzclass.lib`）访问游戏内部对象。
  本仓库不分发框架源码，构建前需自行获取。

```
MIT License

Copyright (c) 2025 PVZClasses

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

## 2. 游戏本体与素材

- 《植物大战僵尸》(Plants vs. Zombies) 及其全部美术、音频、动画、文本素材的
  版权归 **Electronic Arts Inc. / PopCap Games** 所有。
- 本仓库**不包含**任何游戏原始文件（`*.exe`、`*.reanim.compiled`、`*.png` 素材、
  `*.ogg` 音频、`main.pak` 等）。
- 使用本项目需要你自行拥有正版游戏（1.0.0.1051 版本）。

## 3. 字体字形位图

`pvzdll/assets/expfont*/` 下的 PNG 是作者为修复游戏内经验值数字渲染问题而
生成的字形位图。它们是对系统字体的离线渲染结果，仅用于在游戏内绘制数字，
不包含字体文件本身。

## 4. 其他改版项目的素材

本项目**未**包含任何来自第三方改版（如「植物大战僵尸融合版」等）的素材。
若你自行放入此类素材，相关版权与授权责任由你承担。
