# Checks the bundle really works before it's packed into the installer.
$ErrorActionPreference = "Stop"
$app = "build\app"
$py = "$app\python\python.exe"

$desc = (Get-Item "$app\python\Game Hub.exe").VersionInfo.FileDescription
Write-Host "Game Hub.exe describes itself as: $desc"
if ($desc -ne "Game Hub") { throw "Game Hub.exe still has the wrong name: '$desc'" }

& $py -c "import webview, pystray, PIL, clr_loader; print('packages: ok')"
if ($LASTEXITCODE) { throw "packages missing" }
& $py -c "import tkinter; print('window toolkit: Tcl', tkinter.Tcl().eval('info patchlevel'))"
if ($LASTEXITCODE) { throw "tkinter broken" }
& $py -c "import sys; sys.path.insert(0, r'$app'); import game_hub as g; print('Game Hub', g.VERSION, '| sees itself as Game Hub.exe:', g.gui_python().endswith('Game Hub.exe'))"
if ($LASTEXITCODE) { throw "game_hub.py doesn't load" }
