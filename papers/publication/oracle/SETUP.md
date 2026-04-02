# ChatGPT Oracle Bridge — Setup Guide

Automated pipeline that uses your ChatGPT Pro subscription as an AI oracle.
Agents submit tasks (with optional PDF), the browser processes them, results come back automatically.

## Components

| File | Role |
|------|------|
| `oracle_server.py` | Local HTTP server (port 8765) — bridges agents and browser |
| `chatgpt_oracle.user.js` | Tampermonkey userscript — automates ChatGPT interaction |
| `oracle_dispatch.py` | CLI dispatcher — compiles PDF, submits tasks, polls results |

## Setup (5 minutes)

### Step 1: Install Tampermonkey

Install the [Tampermonkey](https://www.tampermonkey.net/) browser extension for Chrome/Edge/Firefox.

### Step 2: Install the userscript

1. Open Tampermonkey Dashboard (click extension icon > Dashboard)
2. Click the `+` tab (new script)
3. Delete the template content
4. Paste the entire contents of `chatgpt_oracle.user.js`
5. Press `Ctrl+S` to save
6. Verify it shows "ChatGPT Oracle Bridge" as enabled

### Step 3: Start the server

```bash
python oracle_server.py
```

Keep this terminal open. The server runs on `http://localhost:8765`.

### Step 4: Open ChatGPT

Navigate to https://chatgpt.com in the same browser where Tampermonkey is installed.
You should see a dark panel in the bottom-right corner: `[Oracle Bridge v2.5] idle`.

### Step 5: Test

```bash
# Quick test (no PDF)
python oracle_dispatch.py --prompt-text "Reply with exactly: ORACLE_OK" --name test_001 --wait --timeout 120

# Full test with PDF
python oracle_dispatch.py --paper path/to/paper_dir --task editorial_review --wait
```

## Task Templates

| Template | What it does |
|----------|-------------|
| `editorial_review` | Full referee report with accept/reject recommendation |
| `deep_research` | Find new theorems and fill mathematical gaps |
| `literature_search` | Identify all related work |
| `proof_verification` | Check every proof for completeness |
| `journal_fit` | Assess fit for target journal |

## CLI Reference

```bash
# With paper PDF (auto-compile)
python oracle_dispatch.py --paper paper_dir/ --task editorial_review --wait

# With existing PDF (skip compile)
python oracle_dispatch.py --paper paper_dir/ --task editorial_review --no-compile --wait

# Custom prompt, no PDF
python oracle_dispatch.py --prompt-text "Your question here" --name my_task --wait

# Custom prompt from file
python oracle_dispatch.py --prompt path/to/prompt.md --name my_task --wait

# Specify model
python oracle_dispatch.py --prompt-text "..." --name my_task --model gpt-4o --wait
```

## Server API

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/submit` | POST | Queue a task: `{"task_id", "prompt", "pdf_base64?", "model?"}` |
| `/task` | GET | Tampermonkey polls this for next task |
| `/result` | POST | Tampermonkey posts ChatGPT response here |
| `/result/<id>` | GET | Poll for task result |
| `/status` | GET | Queue length, pending task, completed count |
| `/ack` | POST | Browser acknowledges task pickup |

## Results

All results are saved to `oracle/done/<task_id>.md` with metadata headers.

## Troubleshooting

| Symptom | Cause | Fix |
|---------|-------|-----|
| Panel not visible | Script not loaded | Refresh chatgpt.com, check Tampermonkey is enabled |
| "Server unreachable" in panel | Server not running | Run `python oracle_server.py` |
| Task queued but not processed | Browser tab not on chatgpt.com | Open/focus the ChatGPT tab |
| Response captured is empty | DOM selectors don't match | Update userscript to latest version |
| Send button not clicked | ChatGPT UI changed | Check panel for "Send debug:" log |
| UnicodeEncodeError on Windows | Console encoding | Result is still saved to file correctly |

## Architecture

```
Your Agent / CLI
      │
      ├── POST /submit ──▶ oracle_server.py (localhost:8765)
      │                         │
      │                    GET /task (Tampermonkey polls)
      │                         │
      │                    ┌────▼─────────────────────┐
      │                    │  chatgpt_oracle.user.js   │
      │                    │  (runs inside Chrome on   │
      │                    │   chatgpt.com)            │
      │                    │                           │
      │                    │  1. Upload PDF            │
      │                    │  2. Enter prompt          │
      │                    │  3. Click send            │
      │                    │  4. Wait for response     │
      │                    │  5. POST /result          │
      │                    └───────────────────────────┘
      │
      └── GET /result/<id> (poll until complete)
```

## Requirements

- Python 3.8+ (no pip dependencies)
- Chrome/Edge/Firefox with Tampermonkey
- ChatGPT Pro subscription (for reliable access)
