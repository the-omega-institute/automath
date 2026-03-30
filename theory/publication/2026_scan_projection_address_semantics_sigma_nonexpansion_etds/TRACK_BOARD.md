# TRACK_BOARD

- Paper: `2026_scan_projection_address_semantics_sigma_nonexpansion_etds`
- Target journal: `Ergodic Theory and Dynamical Systems (ETDS)`
- Current status: `P5_completed`
- Orchestrator: `unassigned`

## Stage Status

- P0 Intake and Contract: `completed`
- P1 Traceability: `completed`
- P2 Research Extension: `completed` -- artifact: `P2_EXTENSION_NOTE_2026-03-30.md`
- P3 Journal-Fit Rewrite: `completed` -- artifact: `P3_REWRITE_NOTE_2026-03-30.md`
- P4 Editorial Review: `completed` -- artifact: `P4_EDITORIAL_REVIEW_2026-03-30.md`
- P5 Integration: `completed` -- triage and edits below
- P6 Lean / Formalization Sync: `completed` -- 0% verified, 27% partial (4/15 active claims have partial Lean support); see `LEAN_SYNC_NOTE_2026-03-30.md`
- P7 Submission Pack: `pending` -- recommended next action

## P5 Triage Decision Log

### P2 recommendations

| # | Recommendation | Decision | Reason |
|---|---|---|---|
| 1 | Single manuscript with strict hierarchy | ACCEPT | Already implemented by P3 rewrite |
| 2 | Front matter: one finite-observation arc | ACCEPT | Already implemented by P3; verified in P5 |
| 3 | Sturmian/hidden-register subordinate | ACCEPT | Already implemented by P3 |

### P3 remaining style issues

| # | Recommendation | Decision | Reason |
|---|---|---|---|
| 1 | Shorten title | DEFER | Current title is descriptive and within ETDS norms; human-judgment call |
| 2 | Move Sturmian illustration to appendix | DEFER | Brief and mathematically clean; referee can request if needed |
| 3 | Cut hidden-entropy subsection | DEFER | Closes the collision loop; already subordinated in section opening |
| 4 | Remove 5 unused bibliography entries | ACCEPT | Removed: MorseHedlund1940, PetersenErgodicTheory, KuipersNiederreiter1974, CoverThomas2006, Renyi1961Measures |

### P4 strongest blockers

| # | Blocker | Decision | Action taken |
|---|---|---|---|
| 1 | Too many coequal payoffs in front matter | ACCEPT | Retitled intro subsection "Role of the open-system sections" (was defensive "Why the open-system lane belongs in this paper"); tightened text to position open-system results as direct consequences of the transfer theorem |
| 2 | Abstract too slow to reach escape-rate point | ACCEPT | P3 already compressed abstract to single paragraph; verified escape rate appears by line 5; no further change needed |
| 3 | Open-system section reads as second thematic center | ACCEPT | Shortened sec_double_budget title from "Survivor Renyi spectra, collision thresholds, and hidden information" to "Survivor Renyi spectra and collision thresholds"; tightened intro subsection language |

## P5 Edits Summary

### Bibliography

- Removed 5 unused entries: MorseHedlund1940, PetersenErgodicTheory, KuipersNiederreiter1974, CoverThomas2006, Renyi1961Measures
- Final bibliography: 17 entries, all cited
- No new citations added (BIB_SCOPE did not identify required additions beyond cleanup)
- Open-system lane literature already embedded in sec_open_system.tex opening paragraph

### Structural edits

- `sec_introduction.tex`: Renamed subsection "Why the open-system lane belongs in this paper" to "Role of the open-system sections"; rewrote text to remove defensive phrasing and position open-system results as direct consequences
- `sec_introduction.tex`: Adjusted Organization paragraph for sec_double_budget to match shortened title
- `sec_double_budget.tex`: Shortened section title from "Survivor Renyi spectra, collision thresholds, and hidden information" to "Survivor Renyi spectra and collision thresholds"

### Verification

- All 14 theorem labels from SOURCE_MAP.md present in manuscript
- Zero dangling \ref{} targets (all refs resolve to existing labels)
- Zero manifesto/AI language detected
- Section flow: preliminaries -> visible words -> structural background -> finite observation/transfer -> open system application -> collision/pressure -> conclusion
- Three main theorems stated in introduction with explicit bridges
- P4 acceptance condition met: front matter makes it impossible to read the paper as a bundle of adjacent manuscripts

## Active claims

- none

## Completed handoffs

- `orchestrator / P2 / P2_EXTENSION_NOTE_2026-03-30.md`
- `orchestrator / P4 / P4_EDITORIAL_REVIEW_2026-03-30.md`
- `rewrite agent / P3 / P3_REWRITE_NOTE_2026-03-30.md`
- `integration agent / P5 / TRACK_BOARD.md (this log)`

## Blocking issues

- recent-paper recon not yet attached (non-blocking for submission)
- Lean formalization coverage remains low (0% verified, 27% partial) -- non-blocking for ETDS submission but noted for future work

## Recommended next action

P7 Submission Pack: compile final PDF, verify clean build with no undefined references, prepare cover letter and submission metadata.
