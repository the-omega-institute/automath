# Registers a Windows Scheduled Task that fires the pipeline watchdog every
# 5 minutes. The task runs the watchdog inside the WSL distro, which also
# boots the distro if it was shut down — so this covers both "supervisor
# died" and "WSL stopped". The watchdog itself is a no-op when the
# supervisor is already alive (see pipeline_watchdog.sh).
#
# Usage:   powershell -ExecutionPolicy Bypass -File register_watchdog_task.ps1
# Remove:  Unregister-ScheduledTask -TaskName 'AutomathPipelineWatchdog' -Confirm:$false

$ErrorActionPreference = 'Stop'

$TaskName = 'AutomathPipelineWatchdog'
$Distro   = 'NyxIDUbuntu2404Cli'
$Watchdog = '/mnt/d/omega/automath/tools/chatgpt-oracle/pipeline_watchdog.sh'
$IntervalMinutes = 5

$action = New-ScheduledTaskAction -Execute 'wsl.exe' `
  -Argument "-d $Distro -e bash -lc $Watchdog"

# Repeat every N minutes, indefinitely, starting at the next minute.
$trigger = New-ScheduledTaskTrigger -Once -At (Get-Date).AddMinutes(1) `
  -RepetitionInterval (New-TimeSpan -Minutes $IntervalMinutes)

# Run in the logged-on user's session (WSL + the Oracle Chrome profile both
# need the interactive desktop session). No stored password required.
$principal = New-ScheduledTaskPrincipal -UserId $env:USERNAME -LogonType Interactive

$settings = New-ScheduledTaskSettingsSet `
  -AllowStartIfOnBatteries -DontStopIfGoingOnBatteries `
  -StartWhenAvailable -MultipleInstances IgnoreNew `
  -ExecutionTimeLimit (New-TimeSpan -Minutes 4)

Register-ScheduledTask -TaskName $TaskName -Action $action -Trigger $trigger `
  -Principal $principal -Settings $settings `
  -Description 'Keeps the Automath paper-pipeline supervisor alive (WSL).' -Force | Out-Null

Write-Host "Registered scheduled task '$TaskName' (every $IntervalMinutes min)."
