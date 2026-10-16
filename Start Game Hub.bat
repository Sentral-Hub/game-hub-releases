@echo off
rem Starts Game Hub without a console window. Game Hub installs its own helper packages on first run.
cd /d "%~dp0"
where pyw >nul 2>nul && (start "" pyw "%~dp0game_hub.py" & exit /b)
where pythonw >nul 2>nul && (start "" pythonw "%~dp0game_hub.py" & exit /b)
echo Python was not found. Install it from https://www.python.org/downloads/
echo and tick "Add python.exe to PATH" during setup, then run this file again.
pause
