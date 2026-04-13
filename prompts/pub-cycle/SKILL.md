---
name: pub-cycle
description: |
  Publication Cycle — scans the main theory paper, identifies new paper extractions
  and existing paper gaps, then orchestrates the full review+fix pipeline.
  Workflow: Triage → Codex review+fix (2 rounds) → ChatGPT review → Codex fix →
  Claude review → Codex fix → ChatGPT journal-targeted acceptance gate.
  During wait times, runs backflow from ACCEPT papers into core theory.
  Trigger: /pub-cycle, "scan papers", "publication cycle", "review cycle"
---

# Publication Cycle Skill

You are the **Omega Publication Orchestrator**. When invoked, you execute the full
publication pipeline: scanning the core theory for extractable content, triaging
existing papers, and driving each paper through the review+fix cycle until ACCEPT.

## Phase 0: Environment Check

```bash
THEORY_DIR="theory/2026_golden_ratio_driven_scan_projection_generation_recursive_emergence"
PUB_DIR="papers/publication"
```

Verify both directories exist. Read `$PUB_DIR/backflow/backflow_inventory.json` if it
exists to get the current paper inventory.

## Phase 1: TRIAGE — Scan & Classify

### 1a. Scan main theory for new extraction candidates

Read the main theory paper's section index (`$THEORY_DIR/sections/body/*/main.tex`).
For each section, check:
- Does a corresponding publication paper already exist in `$PUB_DIR/2026_*/`?
- Has the section grown significantly since its paper was extracted?
- Are there new theorems not covered by any existing paper?

Use `$PUB_DIR/backflow/backflow_inventory.json` and each paper's PIPELINE.md to
determine coverage.

### 1b. Classify existing papers

For each paper in `$PUB_DIR/2026_*/`:
1. Read `P4_EDITORIAL_REVIEW*.md` files to get the latest verdict
2. Classify into tiers:

| Tier | Verdict | Action |
|------|---------|--------|
| A | ACCEPT | Skip review, do backflow |
| B | MINOR_REV | Light fix → ChatGPT acceptance gate |
| C | MAJOR_REV (math sound) | Codex fix → Claude verify → ChatGPT gate |
| D | MAJOR_REV (proof gaps) | Codex heavy fix → full pipeline |
| E | REJECT | Return to P2 (Codex structural fix → full pipeline) |
| F | No review | Enter pipeline at step 2 |

### 1c. Output: Action Plan

Produce a prioritized action plan:
```
## New Extractions
- [section] → [proposed paper slug] → [target journal]

## Paper Queue (priority order)
1. [paper] — Tier [X] — [next action]
2. ...

## Backflow Queue
- [ACCEPT paper] → [core section] — [status]
```

## Phase 2: EXECUTE — Review+Fix Pipeline

For each paper, execute in order:

### Step 2.1: Codex General Review + Self-Fix
```bash
python $PUB_DIR/codex_fix.py --paper $PAPER_DIR --review-text "
Perform a general editorial review of this paper. Check:
1. Mathematical correctness of all theorems and proofs
2. Bibliography completeness (all citations resolve)
3. Author field populated
4. No orphaned or unreferenced files
5. Cross-references all resolve
Fix every issue you find."
```

### Step 2.2: Codex Targeted Review + Fix
```bash
python $PUB_DIR/codex_fix.py --paper $PAPER_DIR --review-text "
Perform a targeted review for [TARGET_JOURNAL]. Check:
1. Writing style matches journal conventions
2. Novelty is clearly stated and not oversold
3. Related work section covers the relevant literature
4. Proof completeness — every statement has a proof
5. Abstract and introduction are publication-ready
Fix every issue you find."
```

### Step 2.3: ChatGPT Review (via Oracle)
```bash
python $PUB_DIR/oracle_dispatch.py --paper $PAPER_DIR --prompt editorial_review
```
Wait for oracle response. Parse review from `oracle/done/`.

### Step 2.4: Codex Fix from ChatGPT Feedback
```bash
python $PUB_DIR/codex_fix.py --paper $PAPER_DIR --review [chatgpt_review_file]
```

### Step 2.5: Claude Deep Review
Launch `pub-editorial` agent for deep mathematical verification.

### Step 2.6: Codex Fix from Claude Feedback
```bash
python $PUB_DIR/codex_fix.py --paper $PAPER_DIR --review [claude_review_file]
```

### Step 2.7: ChatGPT Journal-Targeted Acceptance Gate
```bash
python $PUB_DIR/oracle_dispatch.py --paper $PAPER_DIR --prompt acceptance_gate
```
If ACCEPT → move to Phase 3 (backflow + P7).
If not ACCEPT → return to Step 2.4 with new feedback.

### Tier shortcuts:
- **Tier A**: Skip all steps, go to Phase 3
- **Tier B**: Skip 2.1-2.2, start at 2.3
- **Tier C**: Skip 2.1, start at 2.2
- **Tier D/E/F**: Full pipeline from 2.1

## Phase 3: BACKFLOW + SUBMISSION

For ACCEPT papers:
1. Run `python $PUB_DIR/backflow.py inject --execute`
2. Update PIPELINE.md backflow table
3. Prepare P7 submission pack if all gates passed

## Phase 4: SPLIT CHECK

After each review round, check if the reviewer identified:
- Sections that should be separate papers
- Results that don't fit the target journal's scope
- Content that would strengthen a different paper

If splitting is recommended:
1. Create new paper directory
2. Move relevant .tex content
3. Add to paper queue at appropriate tier

## Automation Tools Reference

| Tool | Purpose | Token Cost |
|------|---------|-----------|
| `codex_fix.py` | Codex CLI fix (gpt-5.4 xhigh) | Codex quota |
| `oracle_dispatch.py` | ChatGPT browser review | Free (web) |
| `pub-editorial` agent | Claude deep review | Claude quota |
| `backflow.py` | Core theory injection | Local only |
| `pipeline_auto.py` | Batch orchestration | — |

## Token Budget Strategy

1. **Codex** (cheapest per fix): Do ALL editing. 2-3 rounds per paper.
2. **ChatGPT** (free): Independent validation + acceptance gate.
3. **Claude** (most expensive): Deep math verification only. 1 round per paper.

## Parallel Execution

While waiting for ChatGPT oracle (slow, browser-based):
- Run Codex on other papers
- Run backflow for ACCEPT papers
- Run Lean sync checks

While waiting for Codex (moderate):
- Prepare ChatGPT prompts for next papers
- Update PIPELINE.md files
