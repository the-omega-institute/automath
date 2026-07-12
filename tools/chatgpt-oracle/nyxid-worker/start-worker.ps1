param(
  [Parameter(Mandatory = $true)]
  [ValidateSet("company_win_work_1", "company_win_work_2", "company_win_work_3")]
  [string]$Label,
  [string]$StateDir = "",
  [int]$ChromePort = 9222,
  [string]$TokenFile = "",
  [string]$ProxyHost = "127.0.0.1",
  [int]$ProxyPort = 40002
)

$ErrorActionPreference = "Stop"
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..\..\..")).Path
if (-not $StateDir) { $StateDir = Join-Path $RepoRoot ".nyxid-oracle" }
if (-not $TokenFile) { $TokenFile = Join-Path $StateDir "company-chatgpt-pro-worker-token.txt" }
$WorkerSource = Join-Path $PSScriptRoot "worker.mjs"
$SafeLabel = $Label -replace '[^A-Za-z0-9_.-]', '_'
$Stdout = Join-Path $StateDir "cdp-worker.$SafeLabel.out.log"
$Stderr = Join-Path $StateDir "cdp-worker.$SafeLabel.err.log"
$PidFile = Join-Path $StateDir "cdp-worker.$SafeLabel.pid"

function Test-TcpPort([string]$HostName, [int]$Port) {
  $client = $null
  try {
    $client = [System.Net.Sockets.TcpClient]::new()
    $async = $client.BeginConnect($HostName, $Port, $null, $null)
    if (-not $async.AsyncWaitHandle.WaitOne(800)) { return $false }
    $client.EndConnect($async)
    return $true
  } catch { return $false } finally { if ($client) { $client.Close() } }
}

if (!(Test-Path -LiteralPath $TokenFile)) { throw "Company worker token file missing: $TokenFile" }
if (!(Test-Path -LiteralPath $WorkerSource)) { throw "Tracked NyxID worker missing: $WorkerSource" }
if (!(Test-TcpPort "127.0.0.1" $ChromePort)) { throw "Chrome CDP is unavailable on 127.0.0.1:$ChromePort" }
if (!(Test-TcpPort $ProxyHost $ProxyPort)) { throw "WARP relay is unavailable at $ProxyHost`:$ProxyPort; run start-shared.ps1 explicitly" }

New-Item -ItemType Directory -Force -Path $StateDir | Out-Null
$marker = [System.Uri]::EscapeDataString($SafeLabel)
$env:NYXID_BASE_URL = "https://nyx-api.chrono-ai.fun"
$env:NYXID_WORKER_TOKEN_FILE = $TokenFile
$env:NYXID_WORKER_LABEL = $Label
$env:NYXID_WORKER_SCRIPT_VERSION = "cdp-2.0-chat-work"
$env:NYXID_CHATGPT_TAB_STORAGE_MARKER = $SafeLabel
$env:NYXID_CHATGPT_TAB_URL_MATCH = "nyxid_oracle_channel=$marker"
$env:CHROME_CDP_URL = "http://127.0.0.1:$ChromePort"
$env:NYXID_STATE_DIR = $StateDir
$env:NYXID_FETCH_PROXY = "http://$ProxyHost`:$ProxyPort"
$env:HTTP_PROXY = "http://$ProxyHost`:$ProxyPort"
$env:HTTPS_PROXY = "http://$ProxyHost`:$ProxyPort"
$env:NO_PROXY = "127.0.0.1,localhost"
$env:no_proxy = "127.0.0.1,localhost"

Remove-Item -LiteralPath $Stdout, $Stderr -Force -ErrorAction SilentlyContinue
$node = (Get-Command node.exe).Source
$process = Start-Process -WindowStyle Hidden -PassThru -WorkingDirectory $PSScriptRoot -FilePath $node -ArgumentList @(
  $WorkerSource, "--label=$Label"
) -RedirectStandardOutput $Stdout -RedirectStandardError $Stderr
Set-Content -NoNewline -LiteralPath $PidFile -Value $process.Id
Write-Host "Started $Label worker PID $($process.Id)"
