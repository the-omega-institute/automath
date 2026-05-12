# NewMath Consumption Index

This index is the Automath receiving surface for NewMath bridge evidence.
It records NewMath-to-Automath candidates, readiness, and blocking
reasons without writing Automath paper or Lean content. Automath durable
paper writes remain behind the Killo/golden distillation lane.

Input source: `gate`.

Selection gate: `1` receivable item(s), `7` blocked or review-only item(s).

## Readiness Summary

| Readiness | Count | Automath meaning |
| --- | ---: | --- |
| `needs_operator_review` | 3 | operator review boundary |
| `blocked_automath_not_ready` | 2 | blocked until Automath target is selected |
| `observe_only` | 2 | observed |
| `ready_for_local_packet` | 1 | review packet candidate |

## Receivable NewMath Inputs

| Source | Kind | Readiness | Priority | Post-gate state | Automath action |
| --- | --- | --- | ---: | --- | --- |
| `the-omega-institute/newmath@origin/auto-dev:tools/bedc-deep/supervisor.py` | `pipeline_status` | `ready_for_local_packet` | low | `awaiting_operator_acceptance` | summarize as review packet; Killo/golden required before paper write |

## Blocked Or Review-Only Inputs

| Source | Kind | Readiness | Priority | Blocking reason |
| --- | --- | --- | ---: | --- |
| `the-omega-institute/newmath@origin/bridge/newmath-automath-consumption:docs/bridge/automath-newmath-ack.jsonl` | `scope_ledger` | `observe_only` | low | observation only |
| `the-omega-institute/newmath@origin/bridge/newmath-automath-consumption:docs/bridge/automath-newmath-failures.jsonl` | `audit_failure` | `observe_only` | low | observation only |
| `the-omega-institute/newmath@origin/codex-auto-dev:lean4/BEDC/Derived/BeliefUp/TasteGate.lean` | `taste_gate_witness` | `needs_operator_review` | low | operator review is required before this can become receivable |
| `the-omega-institute/newmath@origin/codex-auto-dev:lean4/BEDC/Derived/DyadicPrecisionUp/TasteGate.lean` | `taste_gate_witness` | `needs_operator_review` | low | operator review is required before this can become receivable |
| `the-omega-institute/newmath@origin/codex-auto-dev:lean4/BEDC/Derived/FoldMomentKernelUp/TasteGate.lean` | `taste_gate_witness` | `needs_operator_review` | low | operator review is required before this can become receivable |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/banach/intro_and_carrier.tex` | `paper_claim` | `blocked_automath_not_ready` | low | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/banach/singleton_certificate.tex` | `paper_claim` | `blocked_automath_not_ready` | low | Automath receiving theorem or article section has not been selected |

## Policy

- The writeback selection gate admits only `gate_status=gate_passed` and `ready_for_local_packet` records.
- `Input source: synthesis` means review-only evidence, not a deterministic gate pass.
- `needs_operator_review` records a boundary, not acceptance, and is not selected for writeback.
- `blocked_automath_not_ready` means NewMath evidence exists but Automath has not chosen a receiving paper/Lean target; it is never selected as returnable content.
- The post-gate requires operator acceptance before any Killo/golden distillation candidate can be used.
- Automath paper writeback must pass the native Killo/golden distillation and review lane.
- BEDC text, seed stubs, and TasteGate witnesses must not be copied verbatim into Automath paper content.
