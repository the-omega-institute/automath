# Program Board

Root dispatch table for the publication workspace. Each paper has one `PIPELINE.md` with full stage details.

## Pipeline Progress (2026-03-30)

### Wave 1 (Submission-ready)

| Paper | Target | Stage | Status |
|---|---|---|---|
| ETDS (scan projection) | Ergodic Th. Dyn. Sys. | P7 | **SUBMISSION-READY** |
| APAL (conservative extension) | Ann. Pure Appl. Logic | P7 | **SUBMISSION-READY** |
| TAMS (Fibonacci partition) | Trans. AMS | P7 | **SUBMISSION-READY** |

### Wave 2 (Journal rewrite stage)

| Paper | Target | Stage | Status |
|---|---|---|---|
| JFA (circle dimension) | J. Funct. Anal. | P4 | P3 complete, P4 complete; needs P5 |
| ETDS-zeta (dynamical zeta) | Ergodic Th. Dyn. Sys. | P5 | P5 complete; needs P6-P7 |

### Wave 3 (Research extension stage)

| Paper | Target | Stage | Status |
|---|---|---|---|
| Fredholm-Witt (spectral rigidity) | J. Spectral Theory | P2 | P0-P2 complete, 16 uncited bib entries |
| Self-Dual Sync (cyclotomic twists) | IMRN | P2 | P0-P2 complete, verification scripts needed |
| Prime Languages (sofic obstructions) | Monatshefte Math. | P2 | P0-P2 complete, 12+ uncited bib entries |

## Pipeline Stages

| Stage | Description |
|---|---|
| P0 | Intake: scope, target journal, initial assessment |
| P1 | Traceability: theorem inventory, source map |
| P2 | Research extension: deepen results, scope decisions |
| P3 | Journal-fit rewrite: abstract, intro, style for target venue |
| P4 | Editorial review: referee-grade assessment, blockers |
| P5 | Integration: apply P4 fixes |
| P6 | Lean sync: cross-check against lean4/Omega/ |
| P7 | Submission pack: cover letter + checklist |

## File Convention

Each paper directory contains:
- `PIPELINE.md` — all pipeline tracking (stages, theorems, notes) in one file
- `*.tex` + `references.bib` — the manuscript
- `cover_letter_*.txt` + `submission_checklist.md` — submission artifacts (P7)
- `README.md` — original paper description

## Architecture

- **theory/** = expanding knowledge core (all results accumulate here)
- **theory/publication/** = specialized extractions for specific journals
- **lean4/Omega/** = unified formalization library (not per-paper)
