# Risk Register: BEDC Rule 110 Finite Witness Artifacts

## Overclaim Risks

- The paper implies Rule 110 replaces CIC for universal theorem proving.
- The paper hides that finite witness assertions are not universal quantifiers.
- The paper treats partial Cook/Martinez audit findings as irrelevant.
- The paper fails to distinguish cyclic-tag witness checking from Rule 110
  direct-carrier checking.

## Kill Criteria

Do not promote this seed if:

- the abstract does not explicitly say finite witness;
- the limitation ledger is absent;
- artifact commands are not reproducible;
- strict collision-audit failures are neither fixed nor clearly scoped as
  non-blocking diagnostics.

## Current Risk Controls

- `scope_contract.md` fixes the paper unit as a finite artifact paper.
- `limitation_ledger.md` requires the 26/33 collision-audit result to be either
  fixed or disclosed as scoped diagnostic evidence.
- `recheck_plan.md` prevents stale artifact counts from being copied into a
  promoted manuscript without rerun.
- `promotion_checklist.md` blocks active paper creation until a human approves
  the route.
