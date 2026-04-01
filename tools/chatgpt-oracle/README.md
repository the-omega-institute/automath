# ChatGPT Oracle Bridge

Use your ChatGPT Pro subscription as an automated AI oracle from any script or agent.

```
Your Script ──POST──▶ oracle_server.py ◀──poll── Tampermonkey (Chrome)
                           │                           │
                      GET /result              chatgpt.com automation
```

**3 files, 0 dependencies, 5 minutes to set up.**

## Quick Start

### 1. Install Tampermonkey

Install [Tampermonkey](https://www.tampermonkey.net/) for Chrome/Edge/Firefox.

### 2. Install the userscript

1. Tampermonkey Dashboard → `+` (new script)
2. Delete template, paste contents of `chatgpt_oracle.user.js`
3. `Ctrl+S` to save

### 3. Start server

```bash
python oracle_server.py
```

### 4. Open ChatGPT

Go to https://chatgpt.com — you should see the Oracle panel (bottom-right).

### 5. Ask

```bash
# Simple question
python oracle_ask.py "What is the Riemann hypothesis?"

# With PDF
python oracle_ask.py "Review this paper as a referee" --pdf paper.pdf

# From prompt file
python oracle_ask.py --file my_prompt.txt --pdf paper.pdf --name review_v1
```

Results auto-save to `done/<task_id>.md`.

## Files

| File | What | Size |
|------|------|------|
| `oracle_server.py` | HTTP bridge server (port 8765) | ~3 KB |
| `oracle_ask.py` | CLI client — ask & wait | ~3 KB |
| `chatgpt_oracle.user.js` | Browser automation (Tampermonkey) | ~25 KB |

## Requirements

- Python 3.8+ (stdlib only, no pip install)
- Chrome/Edge/Firefox + Tampermonkey
- ChatGPT account (Pro recommended)

## API

Submit tasks programmatically from any language:

```python
import json, urllib.request

# Submit
data = {"task_id": "my_task", "prompt": "Hello", "pdf_base64": "...(optional)"}
urllib.request.urlopen(urllib.request.Request(
    "http://localhost:8765/submit",
    data=json.dumps(data).encode(), headers={"Content-Type": "application/json"}
))

# Poll
resp = urllib.request.urlopen("http://localhost:8765/result/my_task")
result = json.loads(resp.read())  # {"status": "completed", "response": "..."}
```

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/submit` | POST | `{"task_id", "prompt", "pdf_base64?"}` |
| `/task` | GET | Browser polls for next task |
| `/result` | POST | Browser posts response |
| `/result/<id>` | GET | Poll for result |
| `/status` | GET | Queue info |

## Troubleshooting

| Problem | Fix |
|---------|-----|
| Panel not visible | Refresh chatgpt.com, check Tampermonkey enabled |
| "Server unreachable" | Run `python oracle_server.py` |
| Response empty | ChatGPT UI changed — update `chatgpt_oracle.user.js` |
| UnicodeError on Windows | Ignore — result still saved to file |

## License

MIT
