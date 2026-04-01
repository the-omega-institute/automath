# Publication Pipeline Advance

Fully automated publication pipeline. Advances all active papers through P0->P7 without human intervention.

## How to run

1. Run `python papers/publication/pipeline_auto.py status` to see current state
2. Run `python papers/publication/pipeline_auto.py advance-all` to see what needs work
3. For each paper needing advancement, run `python papers/publication/pipeline_auto.py prompt <paper_dir>` to get the agent prompt
4. Launch agents in parallel for independent papers (different papers can run simultaneously)
5. After agents complete, run `python papers/publication/pub_check.py <paper_dir>` for quality gates

## Pipeline stages

| Stage | Agent action | Key deliverable |
|-------|-------------|-----------------|
| P0 | Read paper, create PIPELINE.md | Scope statement, target journal, MSC codes |
| P1 | Extract theorem inventory | Label-statement table in PIPELINE.md |
| P2 | **Deep research**: strengthen theorems, fill gaps, add new results | Improved .tex files with genuine new content |
| P3 | Journal-fit rewrite: abstract, intro, style | .tex files matching target journal conventions |
| P4 | Referee-grade review + pub_check.py | Issue table with severity in PIPELINE.md |
| P5 | Fix all P4 issues | Updated .tex, re-pass pub_check.py |
| P6 | Lean sync: check against lean4/Omega/ | Coverage report in PIPELINE.md |
| P7 | Cover letter + submission checklist | SUBMISSION-READY status |

## Parallel dispatch rules

- Different papers: run in parallel (launch multiple agents)
- Same paper: P0->P1->P2->P3->P4->P5->P6->P7 sequential
- P6 (Lean sync) can run in parallel with P2-P5

## Priority order

1. **Wave 2 close-to-done**: JFA (P5), ETDS-zeta (P6), APAL (P7)
2. **Wave 3 research**: Fredholm-Witt (P3), Self-Dual (P3), Prime Languages (P3)
3. **Wave 4 triage**: Papers at P0_NEEDED — quick assessment, archive skeletons

## Agent prompts

Each stage has a self-contained prompt in `pipeline_auto.py`. The prompt includes:
- Exact file list
- Specific instructions for that stage
- Quality criteria
- What to write/update

Generate with: `python papers/publication/pipeline_auto.py prompt <paper_dir> [--stage P2]`

## ChatGPT Pro enhancement (optional, non-blocking)

After P5, optionally upload the compiled PDF to ChatGPT Pro for an independent review.
This adds credibility but is NOT required for pipeline progression.
Use `oracle_dispatch.py --paper <dir> --task editorial_review` to queue.

## Paper directories

All papers under `papers/publication/`. Run `pipeline_auto.py status` for full listing.
