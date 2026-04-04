# ChatGPT Oracle — Automated Paper Review via Browser Bridge

Submit a task to ChatGPT Pro through the local oracle pipeline (server + Tampermonkey + dispatch).

## Prerequisites

Before first use, ensure:
1. `oracle_server.py` is running: `python papers/publication/oracle_server.py`
2. Tampermonkey userscript `chatgpt_oracle.user.js` is installed and active
3. A ChatGPT Pro tab is open at https://chatgpt.com

## Usage

The user provides a paper directory and/or task type. Execute the appropriate dispatch command.

### Task types

| Task | Description |
|------|-------------|
| `editorial_review` | Full referee report: assessment, novelty, issues, missing refs |
| `deep_research` | Find new theorems, gaps, scope recommendations |
| `literature_search` | Identify all related/competing work |
| `proof_verification` | Verify every proof for completeness/correctness |
| `journal_fit` | Assess fit for target journal |

### Execution steps

1. **Check server**: `curl -s http://localhost:8765/status` — if unreachable, start it:
   ```bash
   python papers/publication/oracle_server.py &
   ```

2. **Dispatch task**: Parse the user's input to determine paper directory and task type, then run:
   ```bash
   python papers/publication/oracle_dispatch.py \
     --paper papers/publication/<paper_dir> \
     --task <task_type> \
     --no-compile \
     --wait
   ```
   - Use `--no-compile` if `main.pdf` already exists
   - Omit `--no-compile` to auto-compile LaTeX first
   - For custom prompts: `--prompt-text "your prompt here"`
   - For non-PDF tasks: omit `--paper`

3. **Report result**: Read the saved file from `papers/publication/oracle/done/<task_id>.md` and summarize key findings to the user.

### Quick test

```bash
python papers/publication/oracle_dispatch.py \
  --prompt-text "Reply with exactly: ORACLE_OK" \
  --name quick_test --wait --timeout 120
```

## Architecture

```
Agent (Claude Code)
  │
  ├─ oracle_dispatch.py ──POST /submit──▶ oracle_server.py (:8765)
  │                                           │
  │                                      GET /task (poll)
  │                                           │
  │                                      ▼
  │                                 chatgpt_oracle.user.js
  │                                 (Tampermonkey in Chrome)
  │                                      │
  │                                 POST /result
  │                                      │
  └─ poll GET /result/<id> ◀─────────────┘
```

## User Input
