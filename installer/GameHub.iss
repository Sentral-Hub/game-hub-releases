; Game Hub's downloadable installer (built with Inno Setup on GitHub's Windows machines)
#define AppVersion GetEnv("GH_VERSION")

[Setup]
AppId={{B6F1C2E4-7A3D-4C59-9E21-5D8A6F3B0C71}
AppName=Game Hub
AppVersion={#AppVersion}
AppVerName=Game Hub {#AppVersion}
AppPublisher=Game Hub
DefaultDirName={localappdata}\Programs\Game Hub
DisableDirPage=yes
DisableProgramGroupPage=yes
PrivilegesRequired=lowest
ArchitecturesAllowed=x64compatible
ArchitecturesInstallIn64BitMode=x64compatible
OutputDir=..\dist
OutputBaseFilename=GameHubSetup
SetupIconFile=..\build\app\game_hub.ico
UninstallDisplayIcon={app}\python\Game Hub.exe
UninstallDisplayName=Game Hub
WizardStyle=modern
Compression=lzma2/ultra64
SolidCompression=yes
CloseApplications=no
MinVersion=10.0

[Tasks]
Name: "desktopicon"; Description: "Add a desktop shortcut"
Name: "startup"; Description: "Start with Windows (so play time is always tracked)"; Flags: unchecked

[Files]
Source: "..\build\app\*"; DestDir: "{app}"; Flags: ignoreversion recursesubdirs createallsubdirs

[Icons]
Name: "{userprograms}\Game Hub"; Filename: "{app}\python\Game Hub.exe"; Parameters: """{app}\game_hub.py"""; WorkingDir: "{app}"; IconFilename: "{app}\game_hub.ico"
Name: "{userdesktop}\Game Hub"; Filename: "{app}\python\Game Hub.exe"; Parameters: """{app}\game_hub.py"""; WorkingDir: "{app}"; IconFilename: "{app}\game_hub.ico"; Tasks: desktopicon

[Run]
Filename: "{app}\python\python.exe"; Parameters: """{app}\game_hub.py"" --enable-startup"; Flags: runhidden; Tasks: startup
Filename: "{app}\python\Game Hub.exe"; Parameters: """{app}\game_hub.py"""; WorkingDir: "{app}"; Description: "Open Game Hub"; Flags: postinstall nowait skipifsilent

[UninstallDelete]
Type: files; Name: "{userstartup}\Game Hub.vbs"
Type: filesandordirs; Name: "{app}"

[Code]
{ Ask a running Game Hub to close (it saves play time first) by leaving it the same note its own installer uses. }
procedure CloseGameHub();
var Pid: AnsiString; Dir: String; I: Integer;
begin
  Dir := ExpandConstant('{userappdata}\GameHub');
  if LoadStringFromFile(Dir + '\running.pid', Pid) then
  begin
    SaveStringToFile(Dir + '\quit.request', Trim(Pid), False);
    for I := 1 to 60 do
    begin
      if not FileExists(Dir + '\running.pid') then Break;
      Sleep(200);
    end;
  end;
end;

function PrepareToInstall(var NeedsRestart: Boolean): String;
begin
  CloseGameHub();
  Result := '';
end;

{ Taking over from Game Hub's older built-in installer: remove its separate Apps entry and files. }
procedure CurStepChanged(CurStep: TSetupStep);
begin
  if CurStep = ssPostInstall then
  begin
    RegDeleteKeyIncludingSubkeys(HKCU, 'Software\Microsoft\Windows\CurrentVersion\Uninstall\GameHub');
    DeleteFile(ExpandConstant('{app}\Uninstall Game Hub.bat'));
  end;
end;

function InitializeUninstall(): Boolean;
begin
  CloseGameHub();
  Result := True;
end;

procedure CurUninstallStepChanged(CurUninstallStep: TUninstallStep);
begin
  if (CurUninstallStep = usPostUninstall) and not UninstallSilent then
    if MsgBox('Also delete your Game Hub data (favorites, collections, play time history and covers)?' + #13#10#13#10 +
              'Keep it if you might reinstall later.', mbConfirmation, MB_YESNO or MB_DEFBUTTON2) = IDYES then
    begin
      DelTree(ExpandConstant('{userappdata}\GameHub'), True, True, True);
      DelTree(ExpandConstant('{localappdata}\GameHub'), True, True, True);
    end;
end;
