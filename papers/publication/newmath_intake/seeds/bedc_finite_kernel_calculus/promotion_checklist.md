# Promotion Checklist: BEDC Finite Kernel Calculus

This seed is intake-only.  Passing this checklist does not promote it; promotion
requires a human decision and a new active `2026_*` directory.

## Intake Completeness

- [x] `seed_packet.md` states the proposed finite-kernel paper unit.
- [x] `source_map.md` pins `D:/omega/newmath` to commit
  `3fb3d6a0641767388a401883062aa522ea0b397b`.
- [x] `theorem_inventory.md` lists theorem families.
- [x] `declaration_inventory_seed.md` records a first exact-declaration seed.
- [x] `scope_contract.md` separates this paper from automation and Rule110.
- [x] `risk_register.md` lists overclaim risks and kill criteria.
- [x] `venue_ladder.md` lists journal and workshop directions.

## Open Before Promotion

- [x] Select a theorem spine from `declaration_inventory_seed.md`.
- [x] Re-check exact Lean target names against the chosen source commit for
  the selected core `Mark`/`Hist`/`Ext`/`Cont`/`Bundle`/`Ask` declarations.
- [x] Write a non-claim registry distinguishing primitive kernel objects from
  downstream mathematical interfaces.
- [x] Decide whether GroundCompiler material is appendix/interface only or a
  section of the main paper; see `groundcompiler_placement_decision.md`.
- [x] Inspect the exact statement of every selected declaration before it is
  quoted in a promoted manuscript; see `exact_statement_note.md`.
- [x] Decide whether the main result needs a new upstream packaging theorem in
  `D:/omega/newmath`.  Current assessment: yes, unless this becomes a modest
  short note.
- [x] Write a source-side work order for the packaging theorem; see
  `upstream_packaging_work_order.md`.
- [x] Record a current local declaration map without replacing the pinned
  source evidence; see `current_declaration_map.md`.
- [x] Record blocker classes for promotion, source work, and venue checks; see
  `blocker_ledger.md`.
- [x] Record a seed-level related-work scaffold; see
  `bibliography_scope_seed.md`.
- [x] Record the only possible short-note route before source packaging; see
  `short_note_route_memo.md`.
- [ ] Add or identify the upstream packaging theorem before journal-style
  promotion.
- [ ] Re-check current live venue options.
- [ ] Human approves promotion and active paper slug.
  The approval must use the exact form
  `promotion <seed> as <active_slug>`.

## Hard Prohibitions Before Promotion

- Do not create a `papers/publication/2026_*` directory.
- Do not add `main.tex` or `PIPELINE.md` to this seed directory.
- Do not run P0-P7 or Stage A/C automation against this seed directory.
