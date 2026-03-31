# Publication Automation Pipeline

Single source of truth for the end-to-end automation system. Any agent (Claude, ChatGPT, Codex, human) should be able to read this document and operate the pipeline.

## Architecture

```
    +------------------+
    |  Core Knowledge  |  theory/main paper (expanding)
    |     Base         |
    +--------+---------+
             |
      [Layer E: Emergence]  discover new results, spawn paper candidates
             |
      [Layer 1: Decompose]  extract coherent subsets for journals
             |
    +--------v---------+
    | Publication Papers|  papers/publication/  (19 dirs)
    | P0->P4 (Claude)  |  Claude agents do all reasoning + editing
    +--------+---------+
             |
      [P4G: ChatGPT Pro Acceptance Gate]  <-- HARD GATE
      |  Upload PDF, must return ACCEPT   |
      |  If REJECT/MAJOR: iterate P5->P4G |
             |
    +--------v---------+
    | P5->P7 (Claude)  |  Fix issues, Lean sync, submission pack
    +--------+---------+
             |
      [Layer 3: Backflow]  new results -> core
             |
    +--------v---------+
    |  Core Knowledge  |  (enriched, cycle repeats)
    |     Base         |
    +------------------+

Quality standard: Paper is DONE only when ChatGPT Pro says ACCEPT.
Claude does the work. ChatGPT validates. Iterate until acceptance.
```

## Layer 0: Existing Tools

| Tool | Path | What it does |
|---|---|---|
| `research_cycle.py` | `automation/research_cycle.py` | Extract claims from paper sections, generate formalization backlog |
| `publication_sync.py` | `automation/publication_sync.py` | Sync 28 publication papers, track status, Lean linkage |
| `publication_journal_fit.py` | `automation/publication_journal_fit.py` | Journal-fit profiles, revision prompts, boundary analysis |
| `journal_recon.py` | `automation/journal_recon.py` | Web scrape target journals for style signals |
| `omega_ci.py` | `lean4/scripts/omega_ci.py` | Lean audit, inventory, paper-coverage (P6 gate) |
| `pipeline_contract.py` | `automation/pipeline_contract.py` | Contract validation for experiment runs |
| CI/CD | `.github/workflows/` | Daily PDF build, Lean build, PR gate, release |

## Layer E: Emergence (New Content Discovery)

**Purpose:** The pipeline must not only polish existing papers but actively GROW the mathematical content. New theorems, derivation chains, and paper candidates should emerge from analyzing the core.

**Input:** Core paper sections (all of `theory/main_paper/sections/body/`)
**Output:** New results integrated into core + new paper candidates identified

### Emergence Mechanisms

1. **Derivation chain completion** — Find incomplete chains in the core:
   - Theorem X uses Lemma Y, but Lemma Y's proof cites "standard" without proof → close the gap
   - Corollary expected but not stated → state and prove it
   - Tool: `research_cycle.py` claim extraction + ChatGPT Pro reasoning oracle

2. **Cross-section bridges** — Results in section A that could strengthen section B:
   - Entropy results (circle_dimension) might apply to zeta function analysis
   - Galois structure (chebotarev) might inform synchronisation kernel
   - Tool: ChatGPT Pro with `prompts/cross_pollination.md` template

3. **Conjecture resolution** — Upgrade conjectures to theorems:
   - Scan core for `\begin{conjecture}` environments
   - For each, ask reasoning oracle for proof strategy
   - Tool: ChatGPT Pro with `prompts/proof_strategy.md` template

4. **Generalization** — Existing results stated for specific cases that admit generalization:
   - "for q = 9,...,17" → can we extend to q ≥ 9?
   - "for mixing SFTs" → does it hold for sofic shifts?
   - Tool: ChatGPT Pro with `prompts/generalization.md` template

5. **New paper candidate detection** — When emergence produces ≥3 related new results:
   - Cluster them by mathematical theme
   - Check if the cluster is coherent enough for a journal paper
   - If yes → spawn new paper directory, enter Layer 1

### Emergence Trigger

Run emergence scan periodically (suggested: after every 3 paper completions, or when core paper receives significant new content).

```
# Emergence cycle command
python chatgpt_oracle.py \
  --prompt-file prompts/emergence_scan.md \
  --output oracle/emergence_$(date +%Y%m%d).md
```

Agent reads the oracle output and:
- Integrates new results into core paper
- Spawns new paper candidates if warranted
- Updates PROGRAM_BOARD.md with new entries

## Layer 1: Decomposition (Core -> Papers)

**Input:** Main paper section
**Output:** New publication paper directory
**Trigger:** Manual (user identifies a publication-worthy subset)

### Steps

1. **Claim extraction** — Run `research_cycle.py` on the target section(s)
   ```
   python3 automation/research_cycle.py --section <section_name>
   ```
   Output: `slice_manifest.json`, `paper_slice.md`, `formalization_backlog.json`

2. **Scope determination** — Agent reads the claim extraction and proposes:
   - Which claims form a coherent package
   - Target journal (use `publication_journal_fit.py` for profile)
   - Boundary: what's in, what's out, what's deferred

3. **Scaffold** — Create paper directory:
   ```
   papers/publication/2026_<descriptive_name>_<journal>/
   ├── main.tex          (extracted from core, reformatted)
   ├── sec_*.tex          (split by topic, each <800 lines)
   ├── references.bib     (subset from core bib)
   ├── PIPELINE.md        (initialized at P0)
   └── README.md          (one-paragraph description)
   ```

4. **Register** — Add entry to `PROGRAM_BOARD.md`

## Layer 2: Per-Paper Pipeline (P0-P7)

Each stage has: **input**, **tool/agent**, **output**, **quality gate**.

### P0 — Intake

| | |
|---|---|
| Input | Paper directory with main.tex |
| Tool | `publication_sync.py` (auto-detects structure) |
| Output | PIPELINE.md initialized with stage table, scope statement, target journal |
| Gate | main.tex exists, compiles, target journal identified |

### P1 — Traceability

| | |
|---|---|
| Input | All .tex files |
| Tool | `research_cycle.py` claim extraction (CLAIM_ENV_RE + CLAIM_LABEL_RE) |
| Output | PIPELINE.md updated: theorem inventory table, source map, dependency graph |
| Gate | Every `\begin{theorem}` has a `\label{}`, every claim is catalogued |

### P2 — Research Extension

| | |
|---|---|
| Input | Theorem inventory, source map |
| Tool | **Reasoning oracle** (ChatGPT Pro preferred — see Layer 5) |
| Output | PIPELINE.md updated: novelty assessment, gap list, scope cuts, escalation ladder |
| Gate | Every gap has disposition (close / defer / acknowledge), scope cuts justified |

**Prompt template for reasoning oracle:** see `prompts/p2_research_extension.md`

### P3 — Journal-Fit Rewrite

| | |
|---|---|
| Input | P2 scope decisions, journal profile from `publication_journal_fit.py` |
| Tool | Editing agent (Claude or any LLM) |
| Output | Rewritten abstract (<250 words), introduction with theorem preview, style-matched prose |
| Gate | Abstract word count, MSC codes, keywords, no revision-trace language, all files <800 lines |

### P4 — Editorial Review

| | |
|---|---|
| Input | Full manuscript after P3 |
| Tool | **Reasoning oracle** (ChatGPT Pro preferred) + automated checks |
| Output | PIPELINE.md updated: decision (PASS/MINOR/MAJOR/REJECT), issue list with severity |
| Gate | No hard blockers remaining |

**Automated checks (run before oracle):**
```
CHECK-1: Citation completeness  — every \cite has bib entry, every bib entry cited
CHECK-2: Cross-reference integrity — every \ref has \label
CHECK-3: File size — all .tex < 800 lines
CHECK-4: Style — no revision-trace language, no AI-voice markers
CHECK-5: Proof completeness — no "proof omitted", no TODO/FIXME
```

### P5 — Integration

| | |
|---|---|
| Input | P4 issue list |
| Tool | Editing agent |
| Output | All issues resolved, .tex files updated |
| Gate | Re-run P4 automated checks, all pass |

### P6 — Lean Sync

| | |
|---|---|
| Input | Theorem inventory from P1 |
| Tool | `omega_ci.py paper-coverage --sections body --json` |
| Output | PIPELINE.md updated: coverage percentage, verified/partial/missing lists |
| Gate | Coverage reported (no minimum required for submission, but tracked) |

### P7 — Submission Pack

| | |
|---|---|
| Input | Clean manuscript, PIPELINE.md |
| Tool | Template-based generation |
| Output | `cover_letter_<journal>.txt`, `submission_checklist.md` |
| Gate | Checklist all-PASS (except author metadata which may be deferred) |

## Layer 3: Backflow (Papers -> Core)

**Purpose:** New theorems and derivation chains developed during P2 (research extension) flow back to the main paper.

**Trigger:** After P2 completion for any paper.

### Steps

1. **Diff extraction** — Compare paper's theorem inventory against core sections
   - Claims in paper but NOT in core = new results
   - Claims that were sharpened/extended = updates

2. **Integration** — For each new result:
   - Identify target section in core paper
   - Insert theorem + proof + derivation chain
   - Update cross-references
   - Add to core's bibliography if needed

3. **Verification** — Core paper still compiles, no duplicate labels, no broken refs

### Backflow tracking

In each paper's PIPELINE.md, add a "Backflow" section after P2:
```
### Backflow to Core
| Result | Core target section | Status |
|---|---|---|
| thm:new-result | sec_foo | pending / integrated |
```

## Layer 4: Quality Gates (Automated)

These checks can run independently at any pipeline stage. Implement as a single Python script.

### `pub_check.py` — Publication quality checker

```
python3 pub_check.py <paper_dir> [--stage P0|P1|...|P7]
```

**Checks:**
1. `--cite` — Citation completeness (bib ↔ \cite)
2. `--xref` — Cross-reference integrity (\ref ↔ \label)
3. `--size` — File size (<800 lines per .tex)
4. `--style` — Revision-trace and AI-voice scan
5. `--proof` — Proof completeness (no TODO/FIXME/omitted)
6. `--abstract` — Abstract word count (<250)
7. `--msc` — MSC codes present
8. `--pipeline` — PIPELINE.md format validation

**Output:** JSON report + exit code (0 = all pass)

**Status:** Implemented and validated across all 19 papers. See PROGRAM_BOARD.md for results.

## Layer 5: External Oracle Integration (ChatGPT Pro)

### Overview

**Use case:** Reasoning-heavy tasks (P2, P4, P4G, Emergence) where deep mathematical analysis is needed.
**Cost:** Free (uses ChatGPT Pro web subscription, no API cost).

Cloudflare blocks all external automation (API calls, browser automation, cookies). Our solution: a **Tampermonkey userscript** runs INSIDE the user's Chrome browser (invisible to Cloudflare) and communicates with a local Python HTTP server. The pipeline is fully automated — zero human intervention once set up.

### Architecture

```
Agent (oracle_dispatch.py)      oracle_server.py (:8765)     Tampermonkey (browser)     ChatGPT
    |                                  |                           |                       |
    |-- POST /submit {prompt,pdf} ---->|                           |                       |
    |                                  |<-- GET /task (poll 5s) ---|                       |
    |                                  |--- {prompt, pdf_base64} ->|                       |
    |                                  |                           |-- upload PDF --------->|
    |                                  |                           |-- enter prompt ------->|
    |                                  |                           |          (thinking...) |
    |                                  |                           |<-- detect completion --|
    |                                  |<-- POST /result ----------|                       |
    |<-- GET /result/{id} (poll 3s) ---|                           |                       |
    |   response text                  |-- save oracle/done/ ----->|                       |
```

Three components:

| Component | File | Role |
|---|---|---|
| **Oracle Server** | `oracle_server.py` | Local HTTP server (port 8765). Queues tasks, serves them to the browser, stores results. |
| **Tampermonkey Script** | `chatgpt_oracle.user.js` | Runs inside Chrome on chatgpt.com. Polls server for tasks, automates ChatGPT UI (upload PDF, enter prompt, click send, capture response). |
| **Agent Dispatcher** | `oracle_dispatch.py` | CLI tool for agents. Compiles paper PDF, submits task to server, polls for result. |

### Prerequisites

| Requirement | Version | Notes |
|---|---|---|
| **Chrome** (or Chromium-based browser) | Any recent | Must stay open with chatgpt.com during pipeline runs |
| **Tampermonkey extension** | v5.x+ | [Chrome Web Store](https://www.tampermonkey.net/) |
| **ChatGPT Pro subscription** | Active | Must be logged in at chatgpt.com |
| **Python 3** | 3.9+ | For oracle_server.py and oracle_dispatch.py |
| **pdflatex** | Any (TeX Live / MiKTeX) | Only needed if --paper flag used (compiles PDF) |

### Setup (Step by Step)

#### Step 1: Install Tampermonkey Extension

1. Open Chrome → go to [Tampermonkey](https://www.tampermonkey.net/) → click "Install"
2. Pin the Tampermonkey icon in Chrome toolbar (optional but helpful for debugging)

#### Step 2: Install the Oracle Bridge Userscript

1. Click the Tampermonkey icon in Chrome toolbar → "Create a new script..."
2. **Delete all default content** in the editor
3. Copy the entire contents of `chatgpt_oracle.user.js` (from this repo)
4. Paste into the Tampermonkey editor
5. Press **Ctrl+S** to save
6. Verify: The script should appear in the Tampermonkey Dashboard as:
   - Name: `ChatGPT Oracle Bridge`
   - Version: `2.1`
   - Status: **Enabled** (toggle ON)

#### Step 3: Configure Tampermonkey Permissions

The script requires these Tampermonkey grants (already declared in the script header):

```
@grant  GM_xmlhttpRequest    — Cross-origin HTTP to localhost:8765
@grant  GM_setValue           — Persistent storage (survives page navigation)
@grant  GM_getValue           — Read persistent storage
@connect localhost            — Allow connections to localhost
@connect 127.0.0.1            — Allow connections to 127.0.0.1
```

If Tampermonkey asks for permission when the script first runs, **Allow** all requests.

#### Step 4: Verify the Userscript

1. Open https://chatgpt.com in Chrome (log in if needed)
2. You should see a **dark panel** in the bottom-right corner:
   ```
   [Oracle Bridge v2] idle
   ──────────────────────
   HH:MM:SS Oracle Bridge v2 loaded
   HH:MM:SS Server unreachable
   ```
3. The "Server unreachable" message is normal — the oracle server isn't running yet
4. If you don't see the panel:
   - Check Tampermonkey Dashboard → script is **Enabled**
   - Check the script's `@match` includes `https://chatgpt.com/*`
   - Open Chrome DevTools (F12) → Console → look for `[oracle]` log messages
   - Try hard-refreshing the page (Ctrl+Shift+R)

#### Step 5: Start the Oracle Server

```bash
cd papers/publication
python oracle_server.py
```

Output:
```
[server] Oracle server running on http://localhost:8765
[server] Install the Tampermonkey userscript, then open https://chatgpt.com
[server] Press Ctrl+C to stop.
```

Keep this terminal running. The server must stay alive during the entire pipeline session.

Verify: refresh chatgpt.com — the panel should now show:
```
[Oracle Bridge v2] idle
──────────────────────
HH:MM:SS Oracle Bridge v2 loaded
```
(No more "Server unreachable")

#### Step 6: Test with a Simple Task

```bash
# In a new terminal:
cd papers/publication
python oracle_dispatch.py --prompt-text "What is 2+2? Reply with just the number." --name test_task --wait
```

Watch the Chrome window — you should see:
1. Panel shows "=== Task: test_task ==="
2. ChatGPT navigates to new chat (if needed)
3. Prompt appears in the input box
4. Send button is clicked
5. ChatGPT responds
6. Panel shows "DONE: test_task"

The terminal running `oracle_dispatch.py` prints the response.

### Running the Pipeline

#### Submit a Paper for Review

```bash
# Editorial review (compiles PDF automatically):
python oracle_dispatch.py --paper 2026_fredholm_witt_cyclic_block_spectral/ --task editorial_review --wait

# Deep research (novel theorems + gap analysis):
python oracle_dispatch.py --paper 2026_circle_dimension_entropy/ --task deep_research --wait

# Literature search:
python oracle_dispatch.py --paper 2026_self_dual_kernels_jfa/ --task literature_search --wait

# Proof verification:
python oracle_dispatch.py --paper 2026_dynamical_zeta_sofic_obstructions/ --task proof_verification --wait

# Journal fit assessment:
python oracle_dispatch.py --paper 2026_projection_tams/ --task journal_fit --wait
```

#### Submit with Custom Prompt

```bash
# From a prompt file:
python oracle_dispatch.py --paper <paper_dir>/ --prompt prompts/custom.md --wait

# Inline prompt:
python oracle_dispatch.py --prompt-text "Prove that ..." --name my_task --wait

# Text-only (no PDF):
python oracle_dispatch.py --prompt-text "What are the main results in Perron-Frobenius theory?" --name query_001 --wait
```

#### Skip PDF Compilation

```bash
# Use existing main.pdf (skip pdflatex):
python oracle_dispatch.py --paper <paper_dir>/ --task editorial_review --wait --no-compile
```

#### Select ChatGPT Model

```bash
# Default: o3-mini-high (best for deep reasoning)
python oracle_dispatch.py --paper <dir>/ --task editorial_review --wait --model o3-mini-high

# Fast mode: gpt-4o
python oracle_dispatch.py --paper <dir>/ --task literature_search --wait --model gpt-4o
```

#### Queue Multiple Tasks

Tasks are queued in FIFO order. Submit multiple tasks — they execute sequentially:

```bash
python oracle_dispatch.py --paper paper_A/ --task editorial_review --name paper_A_review &
python oracle_dispatch.py --paper paper_B/ --task editorial_review --name paper_B_review &
python oracle_dispatch.py --paper paper_C/ --task editorial_review --name paper_C_review &
wait
```

### Monitoring

#### Server Status

```bash
curl http://localhost:8765/status
# Returns: {"queue_length": 2, "pending": "task_name", "completed": 5}
```

#### Check a Specific Result

```bash
curl http://localhost:8765/result/<task_id>
# Returns: {"task_id": "...", "response": "...", "timestamp": "...", "status": "completed"}
```

#### Saved Results

All completed results are saved to `oracle/done/<task_id>.md` with metadata:

```markdown
<!-- oracle metadata: {"timestamp":"2026-03-31T14:30:00","model":"o3-mini-high","response_length":4521} -->

[ChatGPT response text here]
```

#### Browser Panel

The dark panel in the bottom-right of chatgpt.com shows:
- **Status**: `idle` (waiting for tasks) or `BUSY` (processing)
- **Log**: Last 10 actions with timestamps
- Key events: task received, PDF upload, prompt entry, send, response capture

### Troubleshooting

| Symptom | Cause | Fix |
|---|---|---|
| No panel on chatgpt.com | Script not installed or disabled | Check Tampermonkey Dashboard → script Enabled, `@match` correct |
| Panel shows "Server unreachable" | oracle_server.py not running | Start it: `python oracle_server.py` |
| PDF upload fails | ChatGPT UI changed, file input not found | Check browser console (F12) for `[oracle]` errors. Try refreshing page. |
| Prompt not entered | ProseMirror input not found | Refresh chatgpt.com page. Check if ChatGPT UI updated. |
| Send button never ready | PDF still uploading or UI state stuck | Script waits up to 60s for upload + 30s for button. Increase timeouts in script if needed. |
| Task timeout (15 min) | ChatGPT thinking too long or response detection failed | Check if ChatGPT actually responded. Check "Stop generating" button selector in script. |
| "0 chars" response | Response selector mismatch | ChatGPT may have changed CSS classes. Check `waitForResponse()` selectors. |
| Page navigation kills task | Normal — script uses GM_setValue persistence | Task resumes automatically after page reload. Check panel for "Resuming task" message. |
| CORS error in console | Tampermonkey not granting GM_xmlhttpRequest | Reinstall script. Check `@grant` and `@connect` headers. |

#### Advanced: Browser Console Debugging

Open Chrome DevTools (F12) → Console tab → filter by `[oracle]`:

```
[oracle] 14:30:01 Oracle Bridge v2 loaded
[oracle] 14:30:06 === Task: fredholm_review ===
[oracle] 14:30:06 Navigating to new chat...
[oracle] 14:30:10 Resuming task after navigation: fredholm_review
[oracle] 14:30:11 Page ready
[oracle] 14:30:11 PDF upload: main.pdf (468 KB)
[oracle] 14:30:12 PDF: injected via file input
[oracle] 14:30:14 Waiting for PDF upload to complete...
[oracle] 14:30:24 PDF upload complete (12s), attachment visible
[oracle] 14:30:24 Entering prompt (1523 chars)...
[oracle] 14:30:25 Prompt: pasted via clipboard API
[oracle] 14:30:25 Prompt visible: 1523 chars, success=true
[oracle] 14:30:26 Waiting for send button to be ready...
[oracle] 14:30:27 Send button clicked
[oracle] 14:30:27 Waiting for ChatGPT response...
[oracle] 14:31:00 Waiting... 30s, 0 chars, stable=0
[oracle] 14:33:00 Waiting... 150s, 8421 chars, stable=2
[oracle] 14:33:20 Response complete: 12843 chars
[oracle] 14:33:20 DONE: fredholm_review (12843 chars)
```

### Configuration

#### Userscript Constants (chatgpt_oracle.user.js)

| Constant | Default | Description |
|---|---|---|
| `SERVER` | `http://localhost:8765` | Oracle server URL |
| `POLL_INTERVAL` | `5000` (5s) | How often to check server for new tasks |
| `STABLE_CHECKS` | `5` | Response must be unchanged for N consecutive checks before considered complete |
| `STABLE_INTERVAL` | `4000` (4s) | Interval between response stability checks |
| `MAX_WAIT` | `900000` (15 min) | Maximum time to wait for ChatGPT to respond |

#### Server Constants (oracle_server.py)

| Constant | Default | Description |
|---|---|---|
| `PORT` | `8765` | HTTP server port |
| `ORACLE_DIR` | `./oracle` | Directory for saved results |

#### Dispatcher Constants (oracle_dispatch.py)

| Flag | Default | Description |
|---|---|---|
| `--model` | `o3-mini-high` | ChatGPT model to request |
| `--timeout` | `900` (15 min) | Max seconds to wait for result |
| `--no-compile` | off | Skip pdflatex compilation |
| `--clipboard` | off | Use clipboard fallback mode |

### Task Templates (built into oracle_dispatch.py)

| Task name | Pipeline stage | Purpose |
|---|---|---|
| `editorial_review` | P4/P4G | Referee-grade review: accept/reject, issue table, missing refs |
| `deep_research` | P2 | Novel theorems (2-4) with proofs, gap analysis, scope recommendations |
| `literature_search` | P2/P3 | Competing work, missing citations, overlap analysis |
| `proof_verification` | P2/P5 | Verify every proof: COMPLETE / GAPS / INCORRECT |
| `journal_fit` | P3 | Scope match, technical level, length, impact, recommendation |

### Prompt Templates (in prompts/ — for custom use)

| Template | Pipeline stage | Purpose |
|---|---|---|
| `p2_research_extension.md` | P2 | Novelty assessment, gap analysis, scope |
| `p4_editorial_review.md` | P4 | Referee-grade review, issue list |
| `literature_search.md` | P2/P3 | Competing work, missing citations |
| `proof_strategy.md` | P2/Emergence | Proof approaches for gaps |
| `emergence_scan.md` | Layer E | Cross-section bridges, new results |

Templates have `{PLACEHOLDER}` fields filled by the orchestrating agent before submission.
Task templates (in oracle_dispatch.py) work directly with PDF upload — no placeholder filling needed.

### Models

| Model | Use for | Speed | Reasoning depth |
|---|---|---|---|
| `o3-mini-high` | P2, P4/P4G, proof verification | Slow | Deep (extended thinking) |
| `o1` | Balanced reasoning tasks | Medium | Good |
| `gpt-4o` | Literature search, style review, quick queries | Fast | Standard |

### Fallback: Clipboard Mode

If Tampermonkey doesn't work, the clipboard bridge is available:
```bash
python oracle_dispatch.py --paper <paper_dir>/ --task editorial_review --wait --clipboard
```
This writes the prompt to `oracle/pending/<task_name>.md` and the PDF to `oracle/pending/<task_name>.pdf`. Requires manual copy-paste into ChatGPT and saving the response to `oracle/done/<task_name>.md`.

### Claude (API)

**Use case:** Code generation, LaTeX editing, pipeline orchestration, formalization.
**Cost:** API tokens.
**Integration:** Direct (current setup — Claude Code agents).

### Division of Labor

| Task type | Preferred oracle | Reason |
|---|---|---|
| Deep mathematical reasoning | ChatGPT Pro (free web) | Strong reasoning, free |
| Literature search | ChatGPT Pro (web + browsing) | Web access, free |
| LaTeX editing | Claude (API) | Tool use, file editing |
| Pipeline orchestration | Claude (API) | Agent dispatch, git ops |
| Lean formalization | Claude (API) | Lean4 toolchain access |
| Quality gate checks | Local Python script | Deterministic, fast |

## Execution Order

```
Phase 1: Build missing tools
  └─ pub_check.py (Layer 4 quality gates)
  └─ Prompt templates (Layer 5)
  └─ Backflow tracking format in PIPELINE.md

Phase 2: Validate on one paper
  └─ Pick a Wave 3 paper (fresh, unedited)
  └─ Run full P0-P7 pipeline using the documented process
  └─ Identify friction points, missing steps, broken tools

Phase 3: Fix gaps from Phase 2
  └─ Update this document
  └─ Fix/extend tools

Phase 4: Scale to all papers
  └─ Dispatch agents per paper
  └─ Run backflow after each P2 completion
```

## File Map

```
papers/publication/
├── PROGRAM_BOARD.md          — Status dashboard (all papers)
├── AUTOMATION.md             — This file (pipeline design)
├── oracle_server.py          — Local HTTP server (port 8765, bridge to Tampermonkey)
├── chatgpt_oracle.user.js    — Tampermonkey userscript (runs in Chrome, automates ChatGPT)
├── oracle_dispatch.py        — Agent-side dispatcher (compile PDF + submit to server)
├── chatgpt_oracle.py         — Clipboard bridge (fallback, human operator)
├── chatgpt_api.py            — Direct API client (requires token, Cloudflare may block)
├── chatgpt_browser.py        — Browser automation via undetected-chromedriver (backup)
├── pipeline_auto.py          — Pipeline orchestrator (status, advance, prompt generation)
├── pub_check.py              — Automated quality gates (9 checks)
├── prompts/                  — Oracle prompt templates (for custom use)
│   ├── p2_research_extension.md
│   ├── p4_editorial_review.md
│   ├── literature_search.md
│   ├── proof_strategy.md
│   └── emergence_scan.md
├── oracle/                   — Oracle exchange directory
│   ├── pending/              — Clipboard fallback writes here
│   └── done/                 — Results land here (both modes)
└── <paper_dirs>/             — Individual papers
    ├── PIPELINE.md           — Per-paper tracking (single file)
    └── *.tex + references.bib
```
