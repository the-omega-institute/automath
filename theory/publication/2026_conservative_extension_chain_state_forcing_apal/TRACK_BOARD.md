# TRACK_BOARD

- Paper: `2026_conservative_extension_chain_state_forcing_apal`
- Target journal: `Annals of Pure and Applied Logic (APAL)`
- Current status: `planned_batch_1`
- Orchestrator: `unassigned`

## Stage Status

- P0 Intake and Contract: `completed`
- P1 Traceability: `completed`
- P2 Research Extension: `completed`
  - Artifact: `P2_EXTENSION_NOTE_2026-03-30.md`
  - Date: 2026-03-30
- P3 Journal-Fit Rewrite: `pending` -- recommended next
- P4 Editorial Review: `pending`
- P5 Integration: `pending`
- P6 Lean / Formalization Sync: `pending`
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
- target-journal related-work pass not yet recorded (deferred to P3)

## Gap items for P3

1. Add one-paragraph bridge between strict and intrinsic visible quotients
2. Add standing-hypotheses environment at start of gerbe-obstruction subsection
3. Add explicit mapping of Theorems A/B/C to the four-layer chain in the introduction
4. Consider adding a single-branch S2 micro-example to complement the RP2 blind example

## Recommended next owner

P3 Journal-Fit Rewrite agent. Tasks:
- Rewrite abstract, introduction, and conclusion to foreground the 7-theorem A-B-C package
- Close the four presentation gaps identified in P2_EXTENSION_NOTE
- Enforce APAL register: theorem-first prose, no programmatic language, one research question
- Perform the target-journal related-work bibliography pass (see BIB_SCOPE.md)
