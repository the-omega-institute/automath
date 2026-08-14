$ErrorActionPreference = "Continue"
$w = "D:\omega\automath\.nyxid-oracle\nyxid-via-warp.ps1"
$dir = "D:\omega\automath\tools\chatgpt-oracle\sprint"
$prompt = "/mnt/d/omega/automath/tools/chatgpt-oracle/sprint/deepen_prompt.txt"

function Invoke-Nyxid {
  param([string[]]$NyxArgs)
  try { $o = & $w @NyxArgs 2>&1 | Out-String } catch { $o = "" }
  if ($null -eq $o) { $o = "" }
  return $o
}

for ($tick = 1; $tick -le 120; $tick++) {
  # 1. harvest finished results
  foreach ($line in (Get-Content "$dir\sessions.tsv" -ErrorAction SilentlyContinue)) {
    $p = $line -split "`t"
    if ($p.Count -lt 3) { continue }
    $tag = $p[0]; $task = $p[2]
    $outfile = "$dir\result_$tag.md"
    if (Test-Path $outfile) { continue }
    $r = Invoke-Nyxid @("oracle","result",$task)
    if ($r.Length -gt 800 -and $r -notmatch "Task is dispatched") {
      $r | Set-Content -Encoding utf8 $outfile
      Write-Output "[tick $tick] HARVESTED $tag ($($r.Length) chars)"
    }
  }
  # 2. submit next pending if a slot is free
  $st = Invoke-Nyxid @("oracle","status","company-chatgpt-pro")
  $disp = ([regex]::Match($st,'Dispatched:\s+(\d+)')).Groups[1].Value
  $qd   = ([regex]::Match($st,'Queued:\s+(\d+)')).Groups[1].Value
  $inflight = 99
  if ($disp -ne "") { $inflight = [int]$disp + [int]$qd }
  $pend = @(Get-Content "$dir\pending.tsv" -ErrorAction SilentlyContinue | Where-Object { $_.Trim() -ne "" })
  if ($inflight -lt 4 -and $pend.Count -gt 0) {
    $q = $pend[0] -split "`t"
    $pdf = "/mnt/d/omega/automath/papers/publication/" + $q[1] + "/main.pdf"
    Start-Sleep -Seconds 30
    $o = Invoke-Nyxid @("oracle","ask","company-chatgpt-pro","--file",$prompt,"--pdf",$pdf,"--model","chatgpt-pro","--new-conversation","--tag",("sprint_"+$q[0]+"_r1"),"--client-ref",("sprint_"+$q[0]+"_r1"),"--no-wait")
    $t = ([regex]::Match($o,'Task ID:\s+([a-f0-9-]{36})')).Groups[1].Value
    $c = ([regex]::Match($o,'Session:\s+(conv_[a-f0-9]+)')).Groups[1].Value
    if ($t -ne "") {
      Add-Content -Encoding utf8 "$dir\sessions.tsv" ($q[0]+"`t"+$q[1]+"`t"+$t+"`t"+$c)
      $rest = @($pend | Select-Object -Skip 1)
      Set-Content -Encoding utf8 "$dir\pending.tsv" $rest
      Write-Output "[tick $tick] SUBMITTED $($q[0]) task=$t"
    }
  }
  $done = @(Get-ChildItem "$dir\result_*.md" -ErrorAction SilentlyContinue).Count
  Write-Output "[tick $tick] inflight=$inflight harvested=$done pending=$($pend.Count)"
  if ($done -ge 7) { Write-Output "ALL 7 HARVESTED"; break }
  Start-Sleep -Seconds 60
}
