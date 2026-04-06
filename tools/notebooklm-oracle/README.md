# NotebookLM Oracle Bridge

Use Google NotebookLM as an automated content pipeline from any script or agent.

```
Your Script ──POST──> notebooklm_server.py <──poll── Tampermonkey (Chrome)
                           │                           │
                      GET /result           notebooklm.google.com automation
```

**4 files, 0 dependencies, 5 minutes to set up.**

## Quick Start

### 1. Install Tampermonkey

Install [Tampermonkey](https://www.tampermonkey.net/) for Chrome/Edge/Firefox.

### 2. Install the userscript

1. Tampermonkey Dashboard → `+` (new script)
2. Delete template, paste contents of `notebooklm_oracle.user.js`
3. `Ctrl+S` to save

### 3. Start server

```bash
python notebooklm_server.py
```

### 4. Open NotebookLM

Go to https://notebooklm.google.com — you should see the Oracle panel (bottom-left).
Click **Start** to activate polling.

### 5. Submit a task

```bash
# Study guide from paper PDF
python notebooklm_dispatch.py --paper /path/to/paper_dir --type study_guide

# Audio overview
python notebooklm_dispatch.py --paper /path/to/paper_dir --type audio_overview

# Custom chat
python notebooklm_dispatch.py --paper /path/to/paper_dir --type chat --prompt "Summarize key results"

# Submit without waiting
python notebooklm_dispatch.py --paper /path/to/paper_dir --type study_guide --no-wait
```

Results auto-save to `notebooklm/done/<task_id>.md`.

### 6. Full pipeline (optional)

```bash
# Theory → Summary → Slides → Video → Social metadata
python notebooklm_pipeline.py --paper /path/to/paper_dir

# From Lean file
python notebooklm_pipeline.py --lean Omega/Zeta/DynZeta.lean

# From discovery JSON (output of lean4_discovery_export.py)
python notebooklm_pipeline.py --discovery discovery_report.json
```

## Files

| File | What | Port |
|------|------|------|
| `notebooklm_server.py` | HTTP bridge server | 8766 |
| `notebooklm_dispatch.py` | CLI client — submit & wait | — |
| `notebooklm_oracle.user.js` | Browser automation (Tampermonkey) | — |
| `notebooklm_pipeline.py` | 4-stage content pipeline | — |

## No conflict with ChatGPT Oracle

| | ChatGPT Oracle | NotebookLM Oracle |
|---|---|---|
| Port | 8765 | 8766 |
| `@match` | `chatgpt.com/*` | `notebooklm.google.com/*` |
| Panel | bottom-right | bottom-left |

Both can run simultaneously.

## API

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/submit` | POST | `{"task_id", "task_type", "pdf_base64", "pdf_name", "prompt?"}` |
| `/task` | GET | Browser polls for next task |
| `/ack` | POST | Browser acknowledges task |
| `/result` | POST | Browser posts response |
| `/status` | GET | Queue info |

Task types: `study_guide`, `audio_overview`, `chat`, `review`

## Requirements

- Python 3.8+ (stdlib only, no pip install)
- Chrome/Edge/Firefox + Tampermonkey
- Google account with NotebookLM access

## License

MIT
