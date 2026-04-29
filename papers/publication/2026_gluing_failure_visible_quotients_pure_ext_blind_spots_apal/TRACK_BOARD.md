# Track Board: Gluing Failure, Visible Quotients, and Pure-Ext Blind Spots

**Last updated:** 2026-04-04
**Current stage:** P5 Integration (complete)
**Decision:** Ready for P4 re-review

## Resolved Blockers

1. **Bibliography: FIXED.** Added 6 missing bib entries (Hatcher2002, Weibel1994, DummitFoote2004, Giraud1971, Johnstone2002, StacksProject) to references.bib. All 14 citation keys in compiled files now resolve.
2. **Orphaned .tex files: DOCUMENTED.** Four files (sec_multiaxis_refinement.tex, sec_conservativity.tex, sec_observer_spacetime.tex, sec_appendix.tex) are present in the directory but not \input in main.tex. These should be removed from the submission directory before final submission. Not deleted here pending explicit confirmation.
3. **L3/L4 forward references: FIXED.** Rewritten sec_preliminaries.tex to present a three-layer chain L0/L1/L2. Further layers mentioned only in passing as conservative extensions.

## Remaining Items

1. **Orphaned .tex files need deletion before submission** (awaiting confirmation).
2. **R7 (section promotion) DEFERRED.** Promoting subsections 4.7--4.9 to top-level sections is a structural change better handled in a dedicated P3 pass if desired.
3. **R9 (thin bibliography) DEFERRED.** Additional standard references (Vaananen, Abramsky et al. 2015, Breen) could strengthen the bibliography but are not blocking.
4. **3.7 (additional MSC code 18G50) DEFERRED.** Not blocking submission.

## P5 Decision Log

| P4 Issue | Severity | P5 Decision | Action |
|---|---|---|---|
| R1: 6 missing bib entries | BLOCKER | ACCEPT | Added 6 entries to references.bib |
| R2: 4 orphaned .tex files | BLOCKER | ACCEPT (document) | Noted for removal; not deleted without confirmation |
| R3: L3/L4 forward refs | MEDIUM | ACCEPT | Rewrote sec_preliminaries to three-layer chain |
| R4: Standing refinement hypothesis | MEDIUM | ACCEPT | Added Definition (refinement-stability) with label; updated proof reference |
| R5: Thm 4.29 proof tightening | MEDIUM | ACCEPT | Specified concrete model, sort domain, swap automorphism, clarified constants |
| R6: Cofinal-family hypothesis in examples | MEDIUM | ACCEPT | Added one sentence to each of Ex 4.47 (S2) and Ex 4.48 (RP2) |
| R7: Section promotion | MEDIUM | DEFER | Structural change; better in dedicated P3 pass |
| R8: Proof reference wording | MINOR | ACCEPT | Changed "by Definition 4.36" to "by the UCT exact sequence stated in Definition 4.36" |
| 3.4: Intro road-map language | MEDIUM | ACCEPT | Rewrote to say "Within that section" for subsection references |
| 3.5: Empty author block | MEDIUM | ACCEPT | Set author to Haobo Ma, affiliation CHRONOAI PTE. LTD., Singapore |
| 3.7: Additional MSC code | MINOR | DEFER | Not blocking |
| R9: Thin bibliography | MINOR | DEFER | Not blocking |

## Stage History

| Stage | Date | Outcome |
|---|---|---|
| P0 Intake | -- | APAL target |
| P1 Traceability | -- | -- |
| P2 Research Extension | 2026-03-23 | 8 revision points applied (review_notes.txt) |
| P3 Journal-Fit Rewrite | 2026-03-31 | APAL-focused version produced |
| P4 Editorial Review | 2026-04-04 | MAJOR_REVISION -- 2 blockers, 7 medium, 4 minor |
| P5 Integration | 2026-04-04 | 2 blockers fixed, 5 medium fixed, 1 minor fixed; 3 deferred |
