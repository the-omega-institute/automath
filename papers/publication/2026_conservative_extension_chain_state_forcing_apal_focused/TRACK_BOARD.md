# Track Board: Conservative Extension Chain / State Forcing (APAL Focused)

**Last updated:** 2026-04-04
**Current stage:** P5 Integration (bibliography fix)
**Decision:** MAJOR_REVISION (P4 R1) -- bibliography blocker resolved

## Top-3 Blockers

1. ~~**Bibliography broken: 7 missing bib entries.**~~ RESOLVED (P5, 2026-04-04). Added StacksProject, Hatcher2002, Weibel1994, DummitFoote2004, Giraud1971, Johnstone2002, BerghSchnurer2021 to references.bib. All 16 cited keys now have matching bib entries.
2. **PDF not properly compiled.** Requires full pdflatex->bibtex->pdflatex->pdflatex rebuild now that bibliography is complete. Cross-references should resolve after rebuild.
3. **4 orphan .tex files present but not compiled.** sec_appendix.tex, sec_multiaxis_refinement.tex, sec_observer_spacetime.tex, sec_conservativity.tex exist in directory but are not \input-ed in main.tex. Contradicts submission checklist claim.

## Sibling Paper Status

The parent paper `2026_conservative_extension_chain_state_forcing_apal` received MINOR_REVISION at Gate 3 (P4, 2026-04-03). The mathematical content of this focused version is a strict subset of that paper. The MAJOR_REVISION verdict here is driven entirely by bibliographic/build defects introduced during the narrowing process, not by mathematical problems.

## Action Required

1. ~~Add 7 missing bibliography entries to references.bib~~ DONE (P5)
2. Run full build cycle (pdflatex -> bibtex -> pdflatex -> pdflatex)
3. Remove or sequester 4 orphan .tex files
4. Update submission_checklist.md
5. Qualify undefinability conclusion in thm:pointwise-irreducibility
6. Re-enter P4 for second review pass

## P5 Decision Log

| Item | Source | Decision | Reason |
|---|---|---|---|
| Add 7 missing bib entries (B1) | P4 BLOCKER | ACCEPT | All 7 keys cited in .tex files; build cannot succeed without them |
| Rebuild PDF (B2) | P4 BLOCKER | DEFER | Requires manual build; bibliography is now complete |
| Remove orphan .tex files (B3) | P4 MEDIUM | DEFER | Structural change outside P5 bibliography-fix scope |
| Update submission checklist (B4) | P4 MEDIUM | DEFER | Depends on clean build with correct theorem numbers |
| Qualify undefinability (M1) | P4 MEDIUM | DEFER | .tex content change; user instruction says do NOT change .tex files besides references.bib |
| UCT expansion (M2) | P4 MINOR | DEFER | .tex content change; outside scope |
| Section restructuring (M3) | P4 MINOR | DEFER | Structural .tex change; outside scope |

## Stage History

| Stage | Date | Outcome |
|---|---|---|
| P0 Intake | -- | APAL target; focused extraction from parent paper |
| P2 Research | 2026-03-23 | 8 revision points (review_notes.txt) |
| P3 Journal-Fit | 2026-03-31 | APAL-focused version: cut branch aggregation, refinement dynamics, complexity |
| P4 Editorial Review R1 | 2026-04-04 | MAJOR_REVISION -- 2 blockers, 2 medium, 6 minor |
| P5 Integration (bib fix) | 2026-04-04 | Bibliography blocker resolved: 7 entries added to references.bib |
