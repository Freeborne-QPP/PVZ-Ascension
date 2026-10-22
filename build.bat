@echo off
setlocal

REM ============================================================
REM  PVZ Ascension - build script
REM
REM  Usage:
REM    build.bat                     build only
REM    build.bat "D:\Games\PvZ"      build + deploy to game folder
REM
REM  Requirements:
REM    - Visual Studio 2019 / 2022 with "Desktop development with C++"
REM    - PVZClass framework source placed at .\pvzclass\
REM ============================================================

set "ROOT=%~dp0"
if "%ROOT:~-1%"=="\" set "ROOT=%ROOT:~0,-1%"
set "GAMEDIR=%~1"

REM ---- If auto-detection fails, hardcode your VS path here ----
REM      Example: set "VS_MANUAL=D:\Microsoft Visual Studio\2022\Community"
set "VS_MANUAL="

echo ==========================================
echo  PVZ Ascension build   (Release ^| Win32)
echo  Root: %ROOT%
echo ==========================================
echo.

REM ---------- 1. locate Visual Studio ----------
set "VSPATH="
if defined VS_MANUAL (
    set "VSPATH=%VS_MANUAL%"
    echo [i] Using manual VS path.
    goto :vs_ready
)

set "VSWHERE=%ProgramFiles(x86)%\Microsoft Visual Studio\Installer\vswhere.exe"
if exist "%VSWHERE%" (
    for /f "usebackq tokens=*" %%i in (`"%VSWHERE%" -latest -products * -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath`) do set "VSPATH=%%i"
)

if not defined VSPATH (
    echo [ERROR] Could not locate Visual Studio automatically.
    echo.
    echo   Option A: install Visual Studio 2019/2022 with the
    echo             "Desktop development with C++" workload.
    echo   Option B: open build.bat and set VS_MANUAL to your VS folder,
    echo             for example:
    echo               set "VS_MANUAL=D:\Microsoft Visual Studio\2022\Community"
    goto :fail
)

:vs_ready
if not exist "%VSPATH%\VC\Auxiliary\Build\vcvarsall.bat" (
    echo [ERROR] vcvarsall.bat not found under: %VSPATH%
    echo         Check the VS_MANUAL path in build.bat.
    goto :fail
)
echo [OK] Visual Studio: %VSPATH%

call "%VSPATH%\VC\Auxiliary\Build\vcvarsall.bat" x86 >nul
if errorlevel 1 (
    echo [ERROR] Failed to initialise the x86 build environment.
    goto :fail
)
echo [OK] x86 environment ready
echo.

REM ---------- 2. check framework ----------
if not exist "%ROOT%\pvzclass\pvzclass.vcxproj" (
    echo [ERROR] PVZClass framework not found.
    echo.
    echo   Download from: https://github.com/PVZClasses/pvzclass
    echo   Extract it so this file exists:
    echo     %ROOT%\pvzclass\pvzclass.vcxproj
    echo.
    echo   The framework is MIT licensed - see THIRD-PARTY-NOTICES.md
    goto :fail
)
echo [OK] PVZClass framework found
echo.

REM ---------- 3. build ----------
REM VS incremental cache can go stale and silently link an old DLL.
REM Always do a full rebuild for predictable results.
echo [*] Cleaning VS project cache...
if exist "%ROOT%\.vs" rmdir /S /Q "%ROOT%\.vs"

echo [*] Rebuilding solution (this takes a few minutes)...
"%VSPATH%\MSBuild\Current\Bin\MSBuild.exe" "%ROOT%\pvzclass.sln" /p:Configuration=Release /p:Platform=Win32 /t:Rebuild /m:1 /p:UseMultiToolTask=false /v:minimal
if errorlevel 1 (
    echo.
    echo [ERROR] Build failed - see compiler output above.
    goto :fail
)

if not exist "%ROOT%\Release\pvzdll.dll" (
    echo [ERROR] pvzdll.dll was not produced.
    goto :fail
)
echo.
echo [OK] Build succeeded:
echo      %ROOT%\Release\pvzdll.dll
echo.

REM ---------- 4. deploy ----------
if "%GAMEDIR%"=="" (
    echo [i] No game folder given, skipping deploy.
    echo     To deploy, run:  build.bat "D:\Games\PlantsVsZombies"
    goto :done
)
if not exist "%GAMEDIR%\" (
    echo [WARN] Game folder not found: %GAMEDIR%
    goto :done
)

echo [*] Deploying to %GAMEDIR% ...
copy /Y "%ROOT%\Release\pvzdll.dll" "%GAMEDIR%\" >nul
if errorlevel 1 (
    echo [WARN] Failed to copy pvzdll.dll - is the game running?
)

REM Config files are NEVER overwritten, so your custom values survive.
for %%f in (plant_tier plant_attack_speed plant_mechanics plant_cost plant_unlock zombie_mechanics waves) do (
    if not exist "%GAMEDIR%\%%f.ini" copy /Y "%ROOT%\pvzdll\%%f.ini" "%GAMEDIR%\" >nul
)

if not exist "%GAMEDIR%\images" mkdir "%GAMEDIR%\images"
copy /Y "%ROOT%\pvzdll\assets\expfontcoin14\ExpFontGDI_*.png" "%GAMEDIR%\images\" >nul 2>&1
echo [OK] Deployed. Existing .ini files were preserved.
echo.

:done
echo ==========================================
echo  HOW TO RUN
echo   1. Start PlantsVsZombies.exe (v1.0.0.1051) to the main menu
echo   2. Run the injector built by the framework: pvzmain.exe
echo   3. Enter a level and try planting something
echo ==========================================
endlocal
exit /b 0

:fail
echo.
echo Build aborted.
endlocal
exit /b 1
