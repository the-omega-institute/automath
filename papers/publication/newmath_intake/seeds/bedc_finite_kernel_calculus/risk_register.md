# Risk Register: BEDC Finite Kernel Calculus

## Overclaim Risks

- The draft reads as a BEDC manifesto rather than a small formal calculus.
- Derived interfaces are presented as initial primitives.
- Concrete instances dominate the finite-kernel theorem chain.
- The manuscript claims replacement of existing foundations.

## Kill Criteria

Do not promote this seed if the draft lacks:

- exact syntax/rules;
- exact theorem inventory;
- a clear non-claim section;
- a comparison with relevant formal calculi or proof-system literature.

## Current Risk Controls

- `scope_contract.md` blocks manifesto and replacement-foundation claims.
- `declaration_inventory_seed.md` forces exact Lean target names before a
  promoted `THEOREM_LIST.md` exists.
- `promotion_checklist.md` keeps the seed out of active paper automation until
  a human chooses a theorem spine and active slug.

## Additional Journal-Route Kill Criteria

Do not route directly to APAL/LMCS if the paper only lists Lean declarations.
A journal route needs a clean mathematical spine, related-work comparison, and
an explanation of why the finite kernel is conceptually nontrivial.
