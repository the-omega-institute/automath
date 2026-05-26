# ChatGPT Oracle Bridge

Use a ChatGPT browser tab as a local reasoning oracle for automation tasks.

```text
client script --POST--> oracle_server.py <--poll-- Tampermonkey userscript
                         GET /result              chatgpt.com
```

## Quick Start

1. Install Tampermonkey.
2. Install the platform script:
   - Windows: `chatgpt_oracle_windows.user.js`
   - macOS: `chatgpt_oracle_macos.user.js`

   `chatgpt_oracle.user.js` is only a compatibility stub; do not install it as
   the active Oracle script.
3. Start the local server:

```bash
python oracle_server.py
```

4. Open one or more dedicated Oracle tabs. For Automath Project mode, use:

```text
https://chatgpt.com/g/g-p-69f858a02c188191ae7f489459bbf866-automathzheng-liu/project?oracle=1
https://chatgpt.com/g/g-p-69f858a02c188191ae7f489459bbf866-automathzheng-liu/project?oracle=2
https://chatgpt.com/g/g-p-69f858a02c188191ae7f489459bbf866-automathzheng-liu/project?oracle=3
```

Generic non-Project tabs also work with `https://chatgpt.com/?oracle=N`,
but Project mode is preferred when the task should use uploaded PDFs or Project
context.

Tabs without `?oracle=N` stay dormant so normal ChatGPT use is not affected.

After updating the userscript file, open Tampermonkey, replace the installed
script content, save it, and reload every dedicated Oracle tab.

Windows script `v5.18` also checks `/task_status/<id>` while waiting for a
response, so a task cancelled by the supervisor clears local tab state and the
tab resumes polling without a manual refresh.

## Protocol

| Endpoint | Method | Purpose |
|---|---|---|
| `/submit` | POST | Queue a task with `task_id`, `prompt`, optional PDF payload |
| `/task?agent=oracle_1` | GET | Assign or return a pending task for one browser agent |
| `/ack` | POST | Refresh the pending-task lease for the browser agent |
| `/result` | POST | Save a browser response; server resolves the stable task id from `agent_id` |
| `/result/<id>` | GET | Poll for a completed result |
| `/status` | GET | Inspect queue and browser-agent state |

## Health Check

Use the read-only health summarizer when the pipeline appears idle:

```bash
python tools/chatgpt-oracle/pipeline_health.py
```

It combines Oracle `/status`, the supervisor heartbeat, supervisor PID liveness,
board discovery, refill state, and the manual submission queue. A `healthy_idle`
report with `reason=gate_exhausted` means the supervisor and Oracle are alive but
every paper is currently blocked, submitted, parked, or otherwise skipped by the
board gate. In that case, the next action is either a listed manual submission
candidate or refill; it is not a browser refresh or a hard restart. Refill can
use `--refill-project-url` when a ChatGPT Project holds the source context, or
local-context mode when only ordinary Oracle tabs are open. Local-context refill
uses `tools/chatgpt-oracle/research_ledger/research_ledger.jsonl` split seeds
and writes only `papers/publication/_refill_queue.json` for operator review; it
does not auto-create papers or bypass overlap gates. The supervisor section also reports `poll_s` and
`next_tick_eta_s` so an operator can distinguish a quiet 5-minute polling
interval from a stale supervisor. When all candidates are skipped, the discovery
section reports `skip_categories` to show whether the backlog is mostly
submitted, archived or parked, overlap-deferred, stuck for review, publication
ready, or blocked by Stage A. If a paper is marked `C-DONE` or `✅ 可投稿` in
the full board but is missing from the manual submission queue, the report lists
it under `ready_not_manual` instead of silently hiding it in the skipped count.

For machine-readable monitoring:

```bash
python tools/chatgpt-oracle/pipeline_health.py --json
```

For scheduled checks, add `--check`: exit code `0` means healthy or runnable,
`1` means attention needed, and `2` means blocked. A
`ready_not_in_manual_queue` attention result is a board triage problem, not a
process failure: either add the paper to the manual submission queue, mark it as
submitted, or park it explicitly. Refill can still run in local-context mode
while this attention remains, but the ready-not-manual paper should be resolved
before treating the board as green.

To persist a timestamped health sample without changing pipeline state, add
`--snapshot`. This appends one JSONL record to
`tools/chatgpt-oracle/supervisor_logs/health.jsonl`, which is a runtime artifact
and should not be committed.

To summarize recent samples:

```bash
python tools/chatgpt-oracle/pipeline_health.py --history 5
```

For a single ordered monitor command that first records a fresh sample and then
prints the recent trend:

```bash
python tools/chatgpt-oracle/pipeline_health.py --snapshot --history 10
```

Add `--check` to that command when a scheduler should fail on the latest
snapshot's status:

```bash
python tools/chatgpt-oracle/pipeline_health.py --snapshot --history 10 --check
```

If the command is used by an external scheduler, add a freshness bound so stale
history cannot hide a stopped monitor:

```bash
python tools/chatgpt-oracle/pipeline_health.py --snapshot --history 10 --check --max-snapshot-age-s 120
```

## Supervisor Runtime

`pipeline_supervisor.py` writes `tools/chatgpt-oracle/.pipeline_supervisor.pid`
as JSON with the running PID, script name, and start timestamp. A second
supervisor process checks this file before touching `.pipeline_supervisor.stop`;
if the recorded PID is still alive, the duplicate exits and leaves the stop file
intact. This prevents accidental parallel outer loops and preserves operator
stop requests for the already-running supervisor.

To stop the supervisor, create:

```bash
tools/chatgpt-oracle/.pipeline_supervisor.stop
```

The running supervisor removes the stop file during clean shutdown. If
`pipeline_health.py --check` reports `supervisor_pid_missing`,
`supervisor_pid_stale`, `supervisor_process_dead`, or
`supervisor_pid_script_mismatch`, restart the supervisor at a safe boundary
after confirming Oracle has no active queued or busy work. If it reports
`supervisor_code_changed`, use the same safe-boundary restart so the running
supervisor loads the updated code.

## Notes

The distillation pipeline can use this bridge as an optional Stage R deep
research oracle (`--oracle-research`) and as an optional Stage W deepening
research oracle (`--oracle-deepening`). It does not use ChatGPT as a reviewer
and does not let ChatGPT write paper files directly; writeback generation,
review gates, and commit hygiene remain in `tools/distillation/distill.py`.

The bridge URL is `http://127.0.0.1:8765`.  Use the explicit IPv4 loopback
address rather than `localhost`; on some Windows setups `localhost` resolves to
an address that the Python server is not listening on.
