"""Turn the bundled pythonw.exe into "Game Hub.exe" with Game Hub's name and icon (uses Game Hub's own code)."""
import os
import shutil
import sys

app = os.path.abspath(sys.argv[1])
sys.path.insert(0, os.getcwd())
import game_hub as g  # noqa: E402

py = os.path.join(app, "python")
exe = os.path.join(py, "Game Hub.exe")
shutil.copy2(os.path.join(py, "pythonw.exe"), exe)
g.strip_signature(exe)
ico = g.make_icon(os.path.join(app, "game_hub.ico"))
if not ico:
    sys.exit("couldn't make the icon")
group, images = g.icon_resources(open(ico, "rb").read())
g.set_exe_resources(exe, g.version_resource(), group, images)
os.remove(os.path.join(py, "pythonw.exe"))   # everything starts through Game Hub.exe
print("made", exe)
