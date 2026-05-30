# P0 Gate Audit: BEDC Intake Seeds

This audit records the current gate state for the three P0 BEDC seeds.  It is
an intake-only control document, not a daemon queue and not a promotion command.

- audit date: 2026-05-31
- intake root: `papers/publication/newmath_intake`
- source repo: `D:/omega/newmath`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`

## Current Gate State

| Seed | Gate state | Safe automatic work | Work that requires explicit human or external action | Promotion status |
|---|---|---|---|---|
| `bedc_automation_pipeline` | promotion-decision gate | Keep intake notes synchronized; refine bibliography scope and non-claims; re-run `check_intake.py` after edits | Human promotion approval; active slug confirmation; final live venue-page check before submission | May promote only after explicit human command |
| `bedc_finite_kernel_calculus` | source-theorem gate | Maintain theorem-spine summaries and current declaration map; keep GroundCompiler as appendix/interface-only | Source-side work in `D:/omega/newmath` to add or identify a packaging theorem such as `finite_kernel_interface_soundness`; later source update note | Do not promote for journal route before packaging theorem |
| `bedc_rule110_finite_witness` | artifact-rerun gate | Maintain static status map, rerun packet, limitation ledger, and toolchain requirements | Toolchain-equipped dynamic rerun of `make`, `make test`, `make test-collision-audit`, and `make test-scale`; trust-chain table after logs exist | Do not promote before dynamic evidence or a disclosed diagnostic-only scope |

## Deterministic Non-Promotion Rules

Agents must not promote or queue a P0 seed when any of the following holds:

- no explicit human promotion command has named the seed and active slug;
- the seed directory would need `main.tex` or `PIPELINE.md`;
- the action would create a `papers/publication/2026_*` directory;
- the action would cite a newer `D:/omega/newmath` commit without a source
  update note;
- the action would use static Rule110 counts as dynamic artifact validation;
- the action would treat GroundCompiler implementation surfaces as a
  finite-kernel main theorem;
- the action would skip the final live venue check before actual submission.

## Current Next Decisions

1. `bedc_automation_pipeline`: decide whether to promote for CICM 2026
   presentation-only as `2026_auditable_theory_to_paper_pipeline`.
2. `bedc_finite_kernel_calculus`: decide whether to approve source-side
   packaging theorem work in `D:/omega/newmath`.
3. `bedc_rule110_finite_witness`: decide whether to provide or use a
   toolchain-equipped environment for the dynamic artifact rerun.

Until one of these decisions is made, the correct state is intake-only.

## Verification

After editing any P0 seed or index, run:

```powershell
python papers\publication\newmath_intake\check_intake.py
```

The expected result is:

```text
OK: newmath intake seeds are not active paper tracks
```

