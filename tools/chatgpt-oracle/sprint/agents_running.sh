#!/bin/bash
# Is a codex agent still running, and is memory healthy?
#
# `ps aux` in this git-bash sees only its own subprocesses -- 7 lines total, no Windows
# processes at all -- so `ps aux | grep codex` returns 0 whether or not codex is running.
# Step (3) of the tick loop asks for confirmation that the previous agent exited before
# dispatching a new one; that check was structurally incapable of ever saying "yes, running",
# which is the failure mode where two agents edit one paper. Ask Windows instead.
powershell.exe -NoProfile -Command "
  \$c = @(Get-Process -Name codex -ErrorAction SilentlyContinue)
  if (\$c.Count -gt 0) {
    '{0} codex process(es), {1:N0} MB' -f \$c.Count, ((\$c | Measure-Object WorkingSet64 -Sum).Sum/1MB)
  } else { 'no codex running' }
  \$m = Get-Counter '\Memory\Available MBytes','\Memory\Pages/sec' -EA SilentlyContinue
  'available {0:N0} MB, pages/sec {1:N0}' -f \$m.CounterSamples[0].CookedValue, \$m.CounterSamples[1].CookedValue
  \$orph = @(Get-CimInstance Win32_Process -Filter \"Name like '%python%'\" |
    Where-Object { \$_.CommandLine -notmatch 'mcp|chatgpt-oracle' })
  if (\$orph.Count -gt 0) {
    'ORPHAN python x{0}:' -f \$orph.Count
    \$orph | ForEach-Object { '  pid {0}  {1}' -f \$_.ProcessId, \$_.CommandLine }
  } else { 'no orphan python (MCP servers excluded)' }
" 2>/dev/null
