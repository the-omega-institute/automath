param(
  [int]$Port = 9222,
  [string[]]$Agents = @("oracle_1", "oracle_2", "oracle_3", "oracle_4", "oracle_5"),
  [string]$ProfilePath = "D:\omega\automath\.chrome-chatgpt-cdp-profile"
)

$ErrorActionPreference = "Stop"

$Chrome = Join-Path $env:ProgramFiles "Google\Chrome\Application\chrome.exe"
if (!(Test-Path -LiteralPath $Chrome)) {
  $Chrome = Join-Path ${env:ProgramFiles(x86)} "Google\Chrome\Application\chrome.exe"
}
if (!(Test-Path -LiteralPath $Chrome)) {
  throw "Could not find chrome.exe under Program Files."
}

New-Item -ItemType Directory -Force -Path $ProfilePath | Out-Null

$Args = @(
  "--remote-debugging-port=$Port",
  "--remote-debugging-address=127.0.0.1",
  "--user-data-dir=$ProfilePath",
  "--no-first-run",
  "--no-default-browser-check",
  "--new-window"
)

foreach ($AgentId in $Agents) {
  $Args += "https://chatgpt.com/?oracle=$($AgentId -replace '^oracle_', '')"
}

Write-Host "Starting shared Chrome CDP profile:"
Write-Host "  agents:  $($Agents -join ', ')"
Write-Host "  port:    $Port"
Write-Host "  profile: $ProfilePath"

Start-Process -FilePath $Chrome -ArgumentList $Args
