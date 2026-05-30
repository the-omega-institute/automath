# Risk Register: BEDC Automation Pipeline

## Overclaim Risks

- The paper sounds like a general theorem prover or Lean hammer.
- The paper sounds like AI replaces mathematical direction.
- The paper reports theorem counts without quality controls.
- The paper treats journal acceptance as a purely automated process.

## Kill Criteria

Do not promote this seed if the draft lacks:

- a gate-by-gate architecture table;
- at least three concrete failure modes and how the pipeline catches them;
- source-map and theorem-list examples from publication tracks;
- a clear comparison against Lean-auto, ProofWala, and other AI-for-math tools.

## Current Risk Controls

- `scope_contract.md` excludes Lean-hammer, AI-as-proof, and automated
  acceptance claims.
- `gate_table.md` ties each architectural claim to a source path and a failure
  class.
- `failure_modes.md` requires case studies to report both detector and recovery
  action.
- `promotion_checklist.md` blocks creation of a `2026_*` active paper directory
  until a human explicitly approves promotion.

## Additional Kill Criteria Before Journal Route

Do not route this seed directly to JAR/JFR if it has only architecture tables
and no concrete case studies.  A journal route needs either a strong artifact
evaluation or a mature comparison against existing AI-for-formalization systems.
