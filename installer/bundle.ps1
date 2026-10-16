# Builds build\app: a private Python with Game Hub's packages, plus Game Hub itself.
# Runs on GitHub's Windows machines; see .github/workflows/build-installer.yml
$ErrorActionPreference = "Stop"
$ProgressPreference = "SilentlyContinue"

$home_ = python -c "import sys; print(sys.base_prefix)"
$ver   = python -c "import platform; print(platform.python_version())"
$mm    = python -c "import sys; print(f'{sys.version_info[0]}{sys.version_info[1]}')"
$app   = "build\app"
Remove-Item build -Recurse -Force -ErrorAction SilentlyContinue
New-Item -ItemType Directory "$app\python" | Out-Null

# 1. Python's "embeddable" package, matching this machine's Python (or the newest earlier patch that has one)
$p = $ver.Split("."); $patch = [int]$p[2]; $zip = "build\embed.zip"; $got = $null
while ($patch -ge 0 -and -not $got) {
  $try = "$($p[0]).$($p[1]).$patch"
  try { Invoke-WebRequest "https://www.python.org/ftp/python/$try/python-$try-embed-amd64.zip" -OutFile $zip; $got = $try }
  catch { $patch-- }
}
if (-not $got) { throw "No embeddable Python found for $ver" }
Write-Host "Embeddable Python $got (build machine has $ver)"
Expand-Archive $zip "$app\python"

# 2. Let it load packages from Lib\site-packages
$pth = Get-ChildItem "$app\python\python*._pth" | Select-Object -First 1
@("python$mm.zip", ".", "Lib", "Lib\site-packages", "import site") | Set-Content $pth.FullName -Encoding ascii

# 3. Game Hub's packages
python -m pip install --disable-pip-version-check -q --upgrade pip
python -m pip install --disable-pip-version-check -q --target "$app\python\Lib\site-packages" --prefer-binary --no-compile pywebview pystray pillow

# 4. The window toolkit (tkinter) used by the setup screens; the embeddable package leaves it out
Copy-Item "$home_\Lib\tkinter" "$app\python\Lib\tkinter" -Recurse
Get-ChildItem "$home_\DLLs" -Include "_tkinter.pyd","tcl*.dll","tk*.dll","zlib*.dll" -File -Recurse | Copy-Item -Destination "$app\python\"
Copy-Item "$home_\tcl" "$app\python\tcl" -Recurse

# 4b. Leave out what Game Hub never uses, so the download and the install stay small
$sp = "$app\python\Lib\site-packages"
Get-ChildItem $sp -Recurse -Directory -Include "__pycache__", "tests", "test" | Remove-Item -Recurse -Force -ErrorAction SilentlyContinue
Get-ChildItem $sp -Recurse -Directory | Where-Object { $_.FullName -match "clr_loader" -and $_.Name -in "x86", "arm64" } | Remove-Item -Recurse -Force -ErrorAction SilentlyContinue
foreach ($d in "tcl\tk8.6\demos", "tcl\tcl8.6\tzdata") { Remove-Item "$app\python\$d" -Recurse -Force -ErrorAction SilentlyContinue }
"{0:N1} MB bundled" -f ((Get-ChildItem $app -Recurse -File | Measure-Object Length -Sum).Sum / 1MB) | Write-Host

# 5. Game Hub, and "Game Hub.exe" (Python's pythonw.exe with Game Hub's name and icon)
Copy-Item game_hub.py "$app\"
python -m pip install --disable-pip-version-check -q pillow
python installer\make_exe.py $app
