param(
  [ValidateSet("Start", "Status")]
  [string]$Action = "Status",
  [string]$StateDir = "",
  [string]$RelayHost = "127.0.0.1",
  [int]$RelayPort = 40002,
  [int]$WarpPort = 40000
)

$ErrorActionPreference = "Stop"
$RepoRoot = (Resolve-Path (Join-Path $PSScriptRoot "..\..\..")).Path
if (-not $StateDir) { $StateDir = Join-Path $RepoRoot ".nyxid-oracle" }
$WarpCli = "C:\Program Files\Cloudflare\Cloudflare WARP\warp-cli.exe"
$RelayScript = Join-Path $PSScriptRoot "warp-http-proxy.mjs"

function Test-TcpPort([string]$HostName, [int]$Port) {
  $client = $null
  try {
    $client = [System.Net.Sockets.TcpClient]::new()
    $async = $client.BeginConnect($HostName, $Port, $null, $null)
    if (-not $async.AsyncWaitHandle.WaitOne(800)) { return $false }
    $client.EndConnect($async)
    return $true
  } catch {
    return $false
  } finally {
    if ($client) { $client.Close() }
  }
}

if ($Action -eq "Status") {
  $warpStatus = & $WarpCli status 2>&1 | Out-String
  [pscustomobject]@{
    Warp = $warpStatus.Trim()
    Relay = Test-TcpPort $RelayHost $RelayPort
    RelayUrl = "http://$RelayHost`:$RelayPort"
  }
  exit 0
}

if (!(Test-Path -LiteralPath $WarpCli)) { throw "Cloudflare WARP CLI not found: $WarpCli" }
if (!(Test-Path -LiteralPath $RelayScript)) { throw "WARP relay source not found: $RelayScript" }
New-Item -ItemType Directory -Force -Path $StateDir | Out-Null

$service = Get-Service -Name "CloudflareWARP" -ErrorAction SilentlyContinue
if ($service -and $service.Status -ne "Running") {
  Start-Service -Name $service.Name
  $service.WaitForStatus("Running", [TimeSpan]::FromSeconds(15))
}

& $WarpCli proxy port $WarpPort | Out-Null
if ($LASTEXITCODE -ne 0) { throw "Unable to configure WARP proxy port" }
& $WarpCli mode proxy | Out-Null
if ($LASTEXITCODE -ne 0) { throw "Unable to configure WARP proxy mode" }
& $WarpCli connect | Out-Null
if ($LASTEXITCODE -ne 0) { throw "Unable to connect WARP" }

if (-not (Test-TcpPort $RelayHost $RelayPort)) {
  $stdout = Join-Path $StateDir "warp-http-proxy.out.log"
  $stderr = Join-Path $StateDir "warp-http-proxy.err.log"
  $node = (Get-Command node.exe).Source
  $process = Start-Process -WindowStyle Hidden -PassThru -FilePath $node -ArgumentList @(
    $RelayScript, $RelayHost, "$RelayPort", "127.0.0.1", "$WarpPort"
  ) -RedirectStandardOutput $stdout -RedirectStandardError $stderr
  Set-Content -NoNewline -LiteralPath (Join-Path $StateDir "warp-http-proxy.pid") -Value $process.Id
}

$deadline = (Get-Date).AddSeconds(15)
while ((Get-Date) -lt $deadline) {
  if (Test-TcpPort $RelayHost $RelayPort) {
    Write-Host "WARP relay ready at http://$RelayHost`:$RelayPort"
    exit 0
  }
  Start-Sleep -Milliseconds 500
}
throw "WARP relay did not become reachable at $RelayHost`:$RelayPort"
