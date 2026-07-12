param(
  [int]$ChromePort = 9222,
  [string]$StateDir = "",
  [string[]]$WorkerLabels = @("company_win_work_1", "company_win_work_2", "company_win_work_3"),
  [switch]$RestartWorkers
)

$ErrorActionPreference = "Stop"
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..\..\..")).Path
if (-not $StateDir) { $StateDir = Join-Path $RepoRoot ".nyxid-oracle" }
$TokenFile = Join-Path $StateDir "company-chatgpt-pro-worker-token.txt"
$ChromeProfile = Join-Path $RepoRoot ".nyxid-chatgpt-cdp-profile"
$Chrome = "C:\Program Files\Google\Chrome\Application\chrome.exe"
$WarpControl = Join-Path $PSScriptRoot "warp-control.ps1"
$WorkerLauncher = Join-Path $PSScriptRoot "start-worker.ps1"

if (@($WorkerLabels).Count -ne 3 -or (@($WorkerLabels | Sort-Object -Unique) -join ",") -ne ((@("company_win_work_1", "company_win_work_2", "company_win_work_3") | Sort-Object) -join ",")) {
  throw "Shared stack requires exactly company_win_work_1, company_win_work_2, company_win_work_3"
}
if (!(Test-Path -LiteralPath $TokenFile)) { throw "Company token file missing: $TokenFile" }

& powershell.exe -ExecutionPolicy Bypass -File $WarpControl -Action Start -StateDir $StateDir
if ($LASTEXITCODE -ne 0) { throw "Explicit WARP startup failed" }

function Test-Cdp {
  try {
    $null = Invoke-RestMethod -Uri "http://127.0.0.1:$ChromePort/json/version" -TimeoutSec 2
    return $true
  } catch { return $false }
}

if (-not (Test-Cdp)) {
  if (!(Test-Path -LiteralPath $Chrome)) { throw "Chrome not found: $Chrome" }
  New-Item -ItemType Directory -Force -Path $ChromeProfile | Out-Null
  Start-Process -FilePath $Chrome -ArgumentList @(
    "--remote-debugging-port=$ChromePort",
    "--remote-debugging-address=127.0.0.1",
    "--user-data-dir=$ChromeProfile",
    "--no-first-run",
    "--no-default-browser-check",
    "https://chatgpt.com/"
  ) | Out-Null
  $deadline = (Get-Date).AddSeconds(30)
  while ((Get-Date) -lt $deadline -and -not (Test-Cdp)) { Start-Sleep -Milliseconds 500 }
}
if (-not (Test-Cdp)) { throw "Chrome CDP did not become available on port $ChromePort" }

$pages = @(Invoke-RestMethod -Uri "http://127.0.0.1:$ChromePort/json/list" -TimeoutSec 5)
foreach ($Label in $WorkerLabels) {
  $marker = "nyxid_oracle_channel=$([System.Uri]::EscapeDataString($Label))"
  if (-not ($pages | Where-Object { $_.type -eq "page" -and $_.url -like "*$marker*" })) {
    $url = [System.Uri]::EscapeDataString("https://chatgpt.com/?$marker")
    $null = Invoke-RestMethod -Method Put -Uri "http://127.0.0.1:$ChromePort/json/new?$url" -TimeoutSec 10
  }
}

foreach ($Label in $WorkerLabels) {
  $pidFile = Join-Path $StateDir "cdp-worker.$Label.pid"
  $reuse = $false
  if (Test-Path -LiteralPath $pidFile) {
    $pidText = (Get-Content -Raw -LiteralPath $pidFile).Trim()
    if ($pidText -match '^\d+$') {
      $process = Get-Process -Id ([int]$pidText) -ErrorAction SilentlyContinue
      $details = Get-CimInstance Win32_Process -Filter "ProcessId=$pidText" -ErrorAction SilentlyContinue
      $reuse = $process -and $process.ProcessName -eq "node" -and $details.CommandLine -like "*worker.mjs*--label=$Label*"
      if ($RestartWorkers -and $reuse) {
        Stop-Process -Id ([int]$pidText) -Force
        $reuse = $false
      }
    }
  }
  if (-not $reuse) {
    & powershell.exe -ExecutionPolicy Bypass -File $WorkerLauncher -Label $Label -StateDir $StateDir -ChromePort $ChromePort -TokenFile $TokenFile
    if ($LASTEXITCODE -ne 0) { throw "Failed to start worker $Label" }
  }
}

Write-Host "NyxID shared workers ready: $($WorkerLabels -join ', ')"
