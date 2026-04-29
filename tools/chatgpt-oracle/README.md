# ChatGPT Oracle Bridge

Use a ChatGPT browser tab as a local reasoning oracle for automation tasks.

```text
client script --POST--> oracle_server.py <--poll-- Tampermonkey userscript
                         GET /result              chatgpt.com
```

## Quick Start

1. Install Tampermonkey.
2. Install `chatgpt_oracle.user.js`.
3. Start the local server:

```bash
python oracle_server.py
```

4. Open one or more dedicated Oracle tabs:

```text
https://chatgpt.com/?oracle=1
https://chatgpt.com/?oracle=2
https://chatgpt.com/?oracle=3
```

Tabs without `?oracle=N` stay dormant so normal ChatGPT use is not affected.

## Protocol

| Endpoint | Method | Purpose |
|---|---|---|
| `/submit` | POST | Queue a task with `task_id`, `prompt`, optional PDF payload |
| `/task?agent=oracle_1` | GET | Assign or return a pending task for one browser agent |
| `/ack` | POST | Refresh the pending-task lease for the browser agent |
| `/result` | POST | Save a browser response; server resolves the stable task id from `agent_id` |
| `/result/<id>` | GET | Poll for a completed result |
| `/status` | GET | Inspect queue and browser-agent state |

## Notes

The distillation pipeline can use this bridge as an optional Stage R deep
research oracle (`--oracle-research`) and as an optional Stage W deepening
research oracle (`--oracle-deepening`). It does not use ChatGPT as a reviewer
and does not let ChatGPT write paper files directly; writeback generation,
review gates, and commit hygiene remain in `tools/distillation/distill.py`.

The bridge URL is `http://127.0.0.1:8765`.  Use the explicit IPv4 loopback
address rather than `localhost`; on some Windows setups `localhost` resolves to
an address that the Python server is not listening on.
