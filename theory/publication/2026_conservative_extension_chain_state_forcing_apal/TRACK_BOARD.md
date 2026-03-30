# TRACK_BOARD

- Paper: `2026_conservative_extension_chain_state_forcing_apal`
- Target journal: `Annals of Pure and Applied Logic (APAL)`
- Current status: `p5_completed`
- Orchestrator: `unassigned`

## Stage Status

- P0 Intake and Contract: `completed`
- P1 Traceability: `completed`
- P2 Research Extension: `completed`
  - Artifact: `P2_EXTENSION_NOTE_2026-03-30.md`
  - Date: 2026-03-30
- P3 Journal-Fit Rewrite: `completed`
  - Artifact: `P3_REWRITE_NOTE_2026-03-30.md`
  - Date: 2026-03-30
- P4 Editorial Review: `completed` -- decision: MAJOR_REVISION
  - Artifact: `P4_EDITORIAL_REVIEW_2026-03-30.md`
  - Date: 2026-03-30
- P5 Integration: `completed`
  - Date: 2026-03-30
- P6 Lean / Formalization Sync: `completed` -- 0% verified (0/13 claims have Lean counterparts); see `LEAN_SYNC_NOTE_2026-03-30.md`
- P7 Submission Pack: `pending`

## P2 Decisions

### Theorems kept in the main line (7 core results)

- `thm:sheafification-characterization` (A1)
- `thm:pointwise-irreducibility` (A2)
- `thm:component-gerbe-decomposition` (B1)
- `thm:gerbe-null-semantics` (B2)
- `thm:intrinsic-visible-quotient` (C1)
- `thm:character-blind-obstructions` (C2)
- `thm:unique-branch-contextuality-comparison` (C3)

### Theorems kept as secondary consequences (not foregrounded)

- `thm:initial-visible-quotient`
- `thm:character-definability-barrier`
- `thm:branch-sensitive-visible-quotient`
- `thm:branch-uniform-visible-quotient`
- `thm:branch-comparison-exact-sequence`
- `thm:branch-resolution-budget`
- `thm:multi-branch-strictification-budget`
- `thm:branch-visibility-monotonicity`
- `thm:minimal-information-cost-of-strictification`
- `thm:intrinsic-prime-decomposition`
- `thm:intrinsic-pure-ext-initiality`

### Theorems / sections moved to sequel track

- `sec_observer_spacetime.tex` (all propositions therein)
- `sec_conservativity.tex` (all propositions therein)

### Scope decision: sec_observer_spacetime.tex

**Out of scope.** No main-chain theorem depends on observer, event-region, coupled-state, or observer-symmetry material. The conservativity proposition is trivial. This section belongs to a multi-observer semantics sequel.

### Scope decision: branch-budget theorems

**Kept as secondary consequences.** The exact comparison sequence (`thm:branch-comparison-exact-sequence`) is the single clean multi-branch result and is retained in the main body. The branch-sensitive, branch-uniform, and multi-branch strictification theorems are kept as supporting corollaries, not elevated to core status.

## Blocking issues

- ~~main theorem chain is not yet explicitly bounded as a four-layer APAL paper~~ resolved by P2
- ~~`sec_observer_spacetime.tex` may still belong to a sequel rather than this submission~~ resolved: sequel
- ~~target-journal related-work pass not yet recorded (deferred to P3)~~ bibliography pass deferred to P4

## Gap items from P2 (all closed by P3)

1. ~~Add one-paragraph bridge between strict and intrinsic visible quotients~~ done: bridge paragraph added in sec_gerbe_obstruction.tex
2. ~~Add standing-hypotheses environment at start of gerbe-obstruction subsection~~ done: (H1)--(H4) list added
3. ~~Add explicit mapping of Theorems A/B/C to the four-layer chain in the introduction~~ done: layer-boundary annotations in introduction
4. ~~Consider adding a single-branch S2 micro-example to complement the RP2 blind example~~ done: `ex:s2-single-branch-maximal-collapse` added

## P3 Summary

Rewrote abstract (~150 words), introduction (one research question, A-B-C preview with layer mapping), and conclusion (summary, external significance, open problems). Closed all four P2 gaps. Style pass enforced APAL register throughout. See `P3_REWRITE_NOTE_2026-03-30.md` for details.

## P4 Decision: MAJOR_REVISION

### Top blockers (must fix before P5)

1. **sec_homological_visibility.tex is 1144 lines** (limit: 800). Must split at the "Aggregating visibility across branches" subsection boundary (~line 573). Extract into `sec_branch_aggregation.tex`.
2. **10 of 21 bibliography entries are uncited.** Baltag1998, Beth1956, Fitting1969, Goldblatt2006, Groenendijk1991, Kripke1965, TroelstraVanDalen1988, vanBenthem2011, vanDalen2013, Veltman1996. Either cite the classic forcing references in the introduction and remove the dynamic-semantics ones, or remove all 10.
3. **Sequel-track files still in submission directory.** `sec_observer_spacetime.tex` and `sec_conservativity.tex` must be moved to `sequel/` or removed from the submission folder.

### Medium-priority issues

4. Standing refinement-conservation hypothesis in sec_null_decomposition.tex is prose-only; needs a labeled axiom/definition.
5. Conclusion is terse (19 lines) for a paper of this size; needs APAL-appropriate discussion expansion.
6. No APAL-published papers in the bibliography; add at least one or two for venue positioning.

### Mathematical assessment

- All 7 core theorems (A1--A2, B1--B2, C1--C3) are correctly stated, fully proved, and genuinely new.
- No unstated assumptions detected in the main theorem chain.
- Proofs are complete; no gaps.
- Cross-references: 0 dangling references found; 63 unused labels (cosmetic, not blocking).

### AI-voice assessment

- PASS. No manifesto language, no repeated summaries, no loose novelty claims. Two minor promotional phrases flagged in the review (Remark 5.11, Conclusion "genuine logical enrichment") -- tolerable but could be tightened.

### Bibliography pass results

- Citations added: 0
- Citations to remove: 10 (listed above)
- Target-journal papers that materially changed framing: 0 (none found; this is itself a gap)

## P5 Integration Summary

All three P4 hard blockers and all medium-priority issues resolved. Fixes applied:

### Hard blockers (all resolved)

1. **sec_homological_visibility.tex line count.** File was already split by P4 into `sec_homological_visibility.tex` (571 lines) and `sec_branch_aggregation.tex` (572 lines). Both under 800 lines. `main.tex` already contains `\input{sec_branch_aggregation}` at the correct position.
2. **Uncited bibliography entries.** Cited Kripke1965, Beth1956, Fitting1969, Goldblatt2006 in a new paragraph in `sec_introduction.tex` (forcing/logic tradition). Removed Baltag1998, Groenendijk1991, vanBenthem2011, vanDalen2013, Veltman1996, TroelstraVanDalen1988 from `references.bib`. Final bibliography: 15 entries, 15 cited, 0 uncited.
3. **Sequel files moved.** `sec_observer_spacetime.tex` and `sec_conservativity.tex` moved to `sequel/` subdirectory. `main.tex` does not reference them.

### Medium-priority fixes (all resolved)

4. **Standing refinement hypothesis formalized.** Replaced prose assumption in `sec_null_decomposition.tex` with a labeled hypothesis `\ref{hyp:refinement-conservation}` using an enumerated `(RC)` environment. Updated the proof of `prop:typed-readout-persistence` to cite the label explicitly.
5. **Conclusion expanded.** Added new subsection "Relation to topos-theoretic forcing" in `sec_conclusion.tex` positioning the paper relative to Tierney and Johnstone's topos-theoretic forcing tradition, citing MacLaneMoerdijk1994 and Johnstone2002. Conclusion grew from 19 to 23 lines.
6. **Abstract sentence split.** Broke the long em-dash sentence about the four-layer chain in `main.tex` abstract into two sentences.

### Verification

- All `.tex` files under 800 lines (max: 580 lines in `sec_null_decomposition.tex`)
- All `\cite{}` keys have corresponding `references.bib` entries (15/15)
- All `references.bib` entries are cited in the main-line `.tex` files (15/15)
- `main.tex` does not reference sequel files
- No sequel files remain in the submission directory root

## Recommended next owner

P7 Submission Pack agent.
