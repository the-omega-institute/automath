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

## Layer 5: External Oracle Integration

### ChatGPT Pro (Web Interface — Clipboard Bridge + PDF Upload)

**Use case:** Reasoning-heavy tasks (P2, P4, Emergence) where deep mathematical analysis is needed.
**Cost:** Free (uses ChatGPT Pro web subscription, no API cost).
**Integration:** `chatgpt_oracle.py` (clipboard bridge) + `oracle_dispatch.py` (agent dispatcher).

Cloudflare blocks browser automation, so we use a clipboard-based bridge:
- Agent writes prompt (+ optional PDF) to `oracle/pending/`
- Human operator runs `chatgpt_oracle.py --watch` which auto-detects clipboard changes
- Results saved to `oracle/done/` and agent reads them

#### Setup

```bash
# Terminal 1 (human operator — keep running):
cd papers/publication
python chatgpt_oracle.py --watch oracle/ --timeout 900

# Terminal 2 (agents submit tasks):
python oracle_dispatch.py --paper <paper_dir>/ --task editorial_review --wait
```

#### Agent Workflow (oracle_dispatch.py)

```bash
# 1. Submit paper for editorial review (compiles PDF + dispatches):
python oracle_dispatch.py --paper <paper_dir>/ --task editorial_review --wait

# 2. Submit for deep research extension:
python oracle_dispatch.py --paper <paper_dir>/ --task deep_research --wait

# 3. Submit with custom prompt:
python oracle_dispatch.py --paper <paper_dir>/ --prompt prompts/custom.md --wait

# 4. Text-only (no PDF):
python oracle_dispatch.py --prompt-text "Prove that ..." --task reasoning --wait
```

#### Direct Usage (chatgpt_oracle.py)

```bash
# Text-only:
python chatgpt_oracle.py --send prompt.md --recv result.md

# PDF + instruction:
python chatgpt_oracle.py --send prompt.md --pdf paper.pdf --recv result.md

# Compile + send:
python chatgpt_oracle.py --compile paper_dir/ --send prompt.md --recv result.md
```

#### Human Operator Steps (per task in watch mode)

1. Script copies instruction prompt to clipboard, opens ChatGPT + file explorer
2. **If PDF attached:** drag-drop PDF into ChatGPT input box
3. Paste instruction (Ctrl+V), send
4. Wait for ChatGPT response (extended thinking may take minutes)
5. Copy the full response (Ctrl+C) — script auto-detects and saves

#### Models

| Model | Use for | Speed |
|---|---|---|
| `o3-mini-high` | Deep reasoning (P2, P4, proofs) | Slow but thorough |
| `gpt-4o` | Literature search, style review | Fast |
| `o1` | Balanced reasoning tasks | Medium |

#### Task Templates (built into oracle_dispatch.py)

| Task name | Used at | Purpose |
|---|---|---|
| `editorial_review` | P4 | Referee-grade review, issue table, missing refs |
| `deep_research` | P2 | Novel theorems, gap analysis, scope decisions |
| `literature_search` | P2/P3 | Competing work, missing citations |
| `proof_verification` | P2/P5 | Verify every proof, flag gaps |
| `journal_fit` | P3 | Scope match, length, impact assessment |

#### Prompt Templates (in prompts/ — for custom use)

| Template | Used at | Purpose |
|---|---|---|
| `p2_research_extension.md` | P2 | Novelty assessment, gap analysis, scope |
| `p4_editorial_review.md` | P4 | Referee-grade review, issue list |
| `literature_search.md` | P2/P3 | Competing work, missing citations |
| `proof_strategy.md` | P2/Emergence | Proof approaches for gaps |
| `emergence_scan.md` | Layer E | Cross-section bridges, new results |

Templates have `{PLACEHOLDER}` fields filled by the orchestrating agent before submission.
Task templates (in oracle_dispatch.py) work directly with PDF upload — no placeholder filling needed.

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
├── chatgpt_oracle.py         — Clipboard bridge (human operator runs --watch)
├── oracle_dispatch.py        — Agent-side dispatcher (compile PDF + queue tasks)
├── pub_check.py              — Automated quality gates (9 checks)
├── prompts/                  — Oracle prompt templates (for custom use)
│   ├── p2_research_extension.md
│   ├── p4_editorial_review.md
│   ├── literature_search.md
│   ├── proof_strategy.md
│   └── emergence_scan.md
├── oracle/                   — Oracle exchange directory
│   ├── pending/              — Agent writes here (picked up by --watch)
│   └── done/                 — Results land here (agent reads)
└── <paper_dirs>/             — Individual papers
    ├── PIPELINE.md           — Per-paper tracking (single file)
    └── *.tex + references.bib
```
