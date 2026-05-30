# Blocker Ledger: BEDC Finite Kernel Calculus

This ledger is intake-only. It does not promote the seed, does not create an
active paper, and does not assert that the missing packaging theorem exists.

- seed:
  `papers/publication/newmath_intake/seeds/bedc_finite_kernel_calculus`
- source repo: `D:/omega/newmath`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- ledger date: 2026-05-31

## Current Decision

Do not promote this seed for a journal-style standalone logic paper yet.

The current theorem spine is useful but still mostly local: constructor
generation, equality, no-confusion, totality, determinacy, associativity, and
field-projection facts. A standalone paper needs either a source-level packaging
theorem or an explicitly modest workshop/short-note route.

## Blocker Table

| Blocker | Class | Current evidence | Required resolution |
|---|---|---|---|
| Missing manuscript-scale packaging theorem | `newmath-source` | `packaging_theorem_proposal.md`, `upstream_packaging_work_order.md`, `exact_statement_note.md` | Add or identify a theorem such as `finite_kernel_interface_soundness`, or a small theorem family that packages the finite-kernel interface |
| Source verification for any new theorem | `newmath-source` | `upstream_packaging_work_order.md` | Run `lake build`, `bedc_ci.py inventory`, and `bedc_ci.py axiom-purity --strict` after source-side work |
| Pinned commit differs from current local source observation | `source-update` | `current_declaration_map.md` | Use `SOURCE_UPDATE_NOTE_TEMPLATE.md` before adopting a newer source commit |
| Related-work comparison for journal route | `automath-only` | `risk_register.md` kill criteria | Prepare a seed-level bibliography/comparison scope before active journal promotion |
| Short-note route decision | `human-decision` | `packaging_theorem_proposal.md` allows only an explicitly modest route without the packaging theorem | Human must approve a workshop/short-note route and its narrow claim boundary |
| Active slug and promotion command | `human-decision` | `promotion_checklist.md` | Human must name the seed and active slug before any `2026_*` directory is created |
| Live venue validation | `live-web-check` | `venue_ladder.md` and `VENUE_DEADLINES.md` are static snapshots | Re-check current venue pages immediately before route selection or submission |

## Safe Automath-Only Work

The following work can continue inside this seed:

- refine declaration-to-manuscript role tables;
- prepare a seed-level bibliography/comparison scope;
- refine the short-note route decision memo without choosing it for the human;
- keep the GroundCompiler appendix/interface-only boundary explicit;
- prepare a source update note shell without changing the source map.

## Forbidden Before Resolution

Do not:

- create `papers/publication/2026_*` for this seed;
- add `main.tex` or `PIPELINE.md` to this seed;
- claim APAL/LMCS/JAR/JFR readiness from local declaration lists alone;
- treat GroundCompiler implementation surfaces as the main finite-kernel
  theorem;
- silently move from the pinned source commit to the observed local source
  state.

