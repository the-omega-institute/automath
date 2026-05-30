# P0 Decision Packet: Newmath BEDC Intake

This packet collects the current human decisions for the three P0 BEDC seeds.
It is intake-only. It is not a promotion command, not a daemon queue, and not
permission to create an active paper directory.

- packet date: 2026-05-31
- intake root: `papers/publication/newmath_intake`
- source repo: `D:/omega/newmath`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- source-pin drift note: `SOURCE_PIN_STATUS.md`

## Decision Summary

| Seed | Current state | Decision needed | If approved | If deferred |
|---|---|---|---|---|
| `bedc_automation_pipeline` | Ready for human promotion decision | Promote for CICM presentation-only as `2026_auditable_theory_to_paper_pipeline`? | Create one active paper track and assemble the two-page CICM manuscript from the prepared packet | Keep as intake seed; no active paper work |
| `bedc_finite_kernel_calculus` | Source-theorem gate | Approve source-side packaging theorem work, or choose the modest short-note route? | Source-side work records theorem path/name/statement before journal promotion; short-note route uses `short_note_route_memo.md` | Keep as support material for the automation paper |
| `bedc_rule110_finite_witness` | Artifact-rerun gate | Provide or approve a `make` plus C compiler environment for dynamic rerun? | Run the Rule110 suite, fill the trust-chain table, then decide full artifact vs diagnostic route | Keep as static intake package with no artifact-validation claim |

## Decision 1: Automation Pipeline Promotion

Prepared evidence:

- `seeds/bedc_automation_pipeline/cicm_two_page_packet.md`
- `seeds/bedc_automation_pipeline/promotion_decision_memo.md`
- `seeds/bedc_automation_pipeline/active_creation_dry_run.md`
- `seeds/bedc_automation_pipeline/source_decision_note.md`

Approval wording should name both:

- seed: `bedc_automation_pipeline`;
- active slug: `2026_auditable_theory_to_paper_pipeline`.

Without that explicit approval, do not create `papers/publication/2026_*`,
`main.tex`, or `PIPELINE.md`.

## Decision 2: Finite-Kernel Next Route

Prepared evidence:

- `seeds/bedc_finite_kernel_calculus/blocker_ledger.md`
- `seeds/bedc_finite_kernel_calculus/upstream_packaging_work_order.md`
- `seeds/bedc_finite_kernel_calculus/bibliography_scope_seed.md`
- `seeds/bedc_finite_kernel_calculus/short_note_route_memo.md`

Default decision: do not journal-promote before a source-side packaging theorem
or theorem family exists.

Allowed next choices:

- approve source-side work in `D:/omega/newmath` to add or identify a
  packaging theorem such as `finite_kernel_interface_soundness`;
- explicitly choose a modest workshop/short-note route and keep claims within
  `short_note_route_memo.md`;
- defer and use this seed only as supporting evidence for the automation paper.

## Decision 3: Rule110 Artifact Rerun

Prepared evidence:

- `seeds/bedc_rule110_finite_witness/artifact_rerun_packet.md`
- `seeds/bedc_rule110_finite_witness/build_environment_plan.md`
- `seeds/bedc_rule110_finite_witness/evidence_separation_note.md`
- `seeds/bedc_rule110_finite_witness/trust_chain_template.md`
- `seeds/bedc_rule110_finite_witness/diagnostic_route_memo.md`

Default decision: do not promote before dynamic evidence exists.

Allowed next choices:

- provide or approve a toolchain-equipped environment and run the dynamic suite;
- if rerun succeeds, fill `trust_chain_template.md` and consider artifact route;
- if collision audit remains partial or failing, apply `diagnostic_route_memo.md`
  before any route decision;
- defer and keep static evidence as intake-only support material.

## Current Guard

Run after any decision-packet or seed edit:

```powershell
python papers\publication\newmath_intake\check_intake.py
```

Expected result:

```text
OK: newmath intake seeds are not active paper tracks
```
