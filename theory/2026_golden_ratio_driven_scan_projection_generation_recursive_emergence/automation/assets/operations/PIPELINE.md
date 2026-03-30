# Multi-Agent Publication Pipeline

This is the canonical execution model for publication work.

The goal is not to automate mathematical discovery away. The goal is to
turn repeated human prompting into a stable sequence of claimable stages
that multiple agents can execute in parallel without stepping on each
other.

## Stage P0: Intake and Contract

Outputs:

- publication directory exists
- `README.md`
- target journal identified
- `main.tex` and `references.bib` present
- current status recorded

Primary asset sources:

- `publication_sync.py`
- `publication_journal_fit.py`
- `WORKBOARD.md`

## Stage P1: Traceability

Outputs:

- `SOURCE_MAP.md`
- `THEOREM_LIST.md`
- draft-to-source mapping made explicit
- Lean labels or declaration anchors attached where possible

Primary purpose:

- make the paper auditable before any heavy rewriting starts

## Stage P2: Research Extension

Outputs:

- sharpened theorem package
- new publishable conclusions or stronger formulations
- explicit scope cuts for anything not serving the current paper

Primary prompt:

- `01_research_extension.md`

## Stage P3: Journal-Fit Rewrite

Outputs:

- article rewritten in the target venue's register
- title / abstract / introduction / theorem roadmap aligned to recent-paper style
- appendix trimmed to venue-appropriate weight

Primary prompt:

- `02_journal_style_rewrite.md`

## Stage P4: Editorial Review

Outputs:

- accept / major revision / reject style report
- concrete editorial blockers
- explicit cut / merge / rewrite recommendations

Primary prompt:

- `03_editorial_review.md`

## Stage P5: Full Improvement

Outputs:

- integrated final revision after editorial review
- bibliography cleaned
- statement / proof transitions tightened

Primary prompt:

- `04_full_improvement.md`

## Stage P6: Lean / Formalization Sync

Outputs:

- paper labels cross-checked against Lean inventory
- missing formalization backlog updated
- statement mismatches surfaced early

Primary tooling:

- `lean4/scripts/omega_ci.py`
- `publication_sync.py`

## Stage P7: Submission Pack

Outputs:

- final manuscript package
- cover letter / checklist
- journal-fit notes archived
- status promoted in the publication program board

## Handoff Rule

No stage is considered done until its output artifact exists in the
paper directory or the generated workboard directory and the next agent
can continue without re-discovering context.
