# Program Board

Root dispatch table for the publication workspace. See `AUTOMATION.md` for the full pipeline design.

## Pipeline Progress (2026-03-30)

### Wave 1 — Submission-ready (3 papers)

| Paper | Target | Stage | Status |
|---|---|---|---|
| ETDS (scan projection) | Ergodic Th. Dyn. Sys. | P7 | **SUBMISSION-READY** (author metadata blocker) |
| APAL (conservative extension) | Ann. Pure Appl. Logic | P7 | **SUBMISSION-READY** (author metadata blocker) |
| TAMS (Fibonacci partition) | Trans. AMS | P7 | **SUBMISSION-READY** |

### Wave 2 — In pipeline (3 papers)

| Paper | Target | Stage | Status |
|---|---|---|---|
| ETDS-zeta (dynamical zeta) | Ergodic Th. Dyn. Sys. | P5 | P5 complete; needs P6-P7 |
| JFA (circle dimension) | J. Funct. Anal. | P4 | P3+P4 complete; needs P5 |
| Prefix Scan (error boundary) | Dynamical Systems | P5 | Needs audit |

### Wave 3 — Research extension (3 papers)

| Paper | Target | Stage | Status |
|---|---|---|---|
| Fredholm-Witt (spectral rigidity) | J. Spectral Theory | P2 | 16 uncited bib entries |
| Self-Dual Sync (cyclotomic twists) | IMRN | P2 | Verification scripts needed |
| Prime Languages (sofic obstructions) | Monatshefte Math. | P2 | 12+ uncited bib entries |

### Wave 4 — Untracked (10 papers, need triage)

| Dir | Has main.tex | Has PIPELINE.md | Notes |
|---|---|---|---|
| `apal_focused` | Y | N | Variant of APAL — merge or archive? |
| `cubical_stokes_...jdsgt` | Y | N | Needs P0 intake |
| `fibonacci_folding_...` | Y | N | Needs P0 intake |
| `fold_truncation_defect_stokes_...` | Y | N | Needs P0 intake |
| `gluing_failure_...apal` | Y | N | Related to APAL — merge or archive? |
| `group_unification_...` | N | N | No main.tex — skeleton only? |
| `JphisComm` | Y | N | Needs P0 intake |
| `recursive_addressing_...tac` | Y | N | Needs P0 intake |
| `yang_lee_quartic_...` | Y | N | Needs P0 intake |
| `zeta_completion_xi_zero_audit` | N | N | No main.tex — skeleton only? |

## pub_check.py Results (2026-03-30)

Full P7 gate scan across all papers:

| Check | Pass | Fail | Systemic? |
|---|---|---|---|
| citation_completeness | 4 | 15 | **YES — #1 priority** |
| pipeline_md | 10 | 9 | YES — Wave 4 papers |
| msc_codes | 11 | 8 | YES — Wave 4 papers |
| style | 12 | 7 | Moderate |
| claim_labels | 16 | 3 | Low |
| crossref_integrity | 17 | 2 | Low |
| file_size | 18 | 1 | Low |
| abstract | 17 | 2 | Low |
| proof_completeness | 19 | 0 | None |

## Pipeline Stages

| Stage | Description | Tool |
|---|---|---|
| P0 | Intake: scope, target journal | `publication_sync.py` |
| P1 | Traceability: theorem inventory, source map | `research_cycle.py` |
| P2 | Research extension: deepen results | ChatGPT oracle + agent |
| P3 | Journal-fit rewrite: abstract, intro, style | Agent (Claude/etc) |
| P4 | Editorial review: referee-grade assessment | ChatGPT oracle + `pub_check.py` |
| P5 | Integration: apply P4 fixes | Agent |
| P6 | Lean sync: cross-check against lean4/Omega/ | `omega_ci.py` |
| P7 | Submission pack: cover letter + checklist | Template + agent |

## File Convention

Each paper directory contains:
- `PIPELINE.md` — all pipeline tracking in one file
- `*.tex` + `references.bib` — the manuscript
- `cover_letter_*.txt` + `submission_checklist.md` — P7 artifacts
- `oracle/` — ChatGPT Pro reasoning outputs (when used)

## Architecture

- **theory/** = expanding knowledge core (all results accumulate here)
- **papers/publication/** = specialized extractions for specific journals
- **papers/publication/AUTOMATION.md** = pipeline design and tooling
- **lean4/Omega/** = unified formalization library (not per-paper)
