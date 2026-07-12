$ErrorActionPreference = "Stop"

$Root = $PSScriptRoot
$Shared = Get-Content -Raw -LiteralPath (Join-Path $Root "start-shared.ps1")
$Worker = Get-Content -Raw -LiteralPath (Join-Path $Root "start-worker.ps1")
$Warp = Get-Content -Raw -LiteralPath (Join-Path $Root "warp-control.ps1")

function Assert-Contains([string]$Text, [string]$Needle, [string]$Message) {
  if (-not $Text.Contains($Needle)) { throw $Message }
}

function Assert-NotContains([string]$Text, [string]$Needle, [string]$Message) {
  if ($Text.Contains($Needle)) { throw $Message }
}

Assert-Contains $Shared '"company_win_work_1", "company_win_work_2", "company_win_work_3"' "shared labels are not fixed"
Assert-NotContains $Shared '"tab_1"' "legacy local labels remain in shared launcher"
Assert-Contains $Shared 'company-chatgpt-pro-worker-token.txt' "company token is not the default"
Assert-Contains $Shared 'warp-control.ps1' "shared launcher does not explicitly own WARP startup"
Assert-Contains $Warp 'warp-cli.exe' "WARP controller does not use warp-cli"
Assert-Contains $Warp ' connect' "WARP controller cannot connect explicitly"
Assert-NotContains $Worker 'warp-cli' "individual worker controls WARP"
Assert-NotContains $Worker ' connect' "individual worker attempts a network connect command"
Assert-Contains $Worker 'worker.mjs' "individual launcher does not use tracked worker source"
Assert-Contains $Worker 'NYXID_STATE_DIR' "worker does not receive local state directory"
Assert-Contains $Warp '127.0.0.1' "relay is not localhost-only"

Write-Host "launcher static tests passed"
