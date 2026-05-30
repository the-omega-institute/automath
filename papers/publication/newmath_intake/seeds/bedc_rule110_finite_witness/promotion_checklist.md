# Promotion Checklist: BEDC Rule 110 Finite Witness Artifacts

This seed is intake-only.  Passing this checklist does not promote it; promotion
requires a human decision and a new active `2026_*` directory.

## Intake Completeness

- [x] `seed_packet.md` states the artifact paper unit.
- [x] `source_map.md` pins `D:/omega/newmath` to commit
  `3fb3d6a0641767388a401883062aa522ea0b397b`.
- [x] `artifact_inventory.md` records reported counts from `rule110/STATUS.md`.
- [x] `scope_contract.md` separates finite witness claims from universal claims.
- [x] `limitation_ledger.md` records the collision-audit limitation and
  forbidden claims.
- [x] `recheck_plan.md` lists pre-promotion commands and counts.
- [x] `risk_register.md` lists overclaim risks and kill criteria.
- [x] `venue_ladder.md` lists artifact and journal routes.

## Open Before Promotion

- [ ] Re-run artifact commands at the chosen source commit.  Current Windows
  environment has no `make`; see `recheck_results.md`.
- [ ] Recompute manifest counts after `make test` materialization.  Static
  source counts were recomputed, but generated manifests are not materialized.
- [ ] Decide whether collision-audit failures are blockers or scoped
  diagnostics.
- [ ] Write a trust-chain table with final LOC/count values.
- [ ] Re-check live CICM/artifact/workshop venue pages.
- [ ] Human approves promotion and active paper slug.

## Hard Prohibitions Before Promotion

- Do not create a `papers/publication/2026_*` directory.
- Do not add `main.tex` or `PIPELINE.md` to this seed directory.
- Do not run P0-P7 or Stage A/C automation against this seed directory.
