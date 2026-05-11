# NewMath Consumption Index

This index is the Automath receiving surface for NewMath bridge evidence.
It records NewMath-to-Automath candidates, readiness, and blocking
reasons without writing Automath paper or Lean content. Automath durable
paper writes remain behind the Killo/golden distillation lane.

Input source: `gate`.

Selection gate: `1` receivable item(s), `44` blocked or review-only item(s).

## Readiness Summary

| Readiness | Count | Automath meaning |
| --- | ---: | --- |
| `blocked_automath_not_ready` | 40 | blocked until Automath target is selected |
| `needs_operator_review` | 4 | operator review boundary |
| `ready_for_local_packet` | 1 | review packet candidate |

## Receivable NewMath Inputs

| Source | Kind | Readiness | Score | Post-gate state | Automath action |
| --- | --- | --- | ---: | --- | --- |
| `the-omega-institute/newmath@origin/auto-dev:tools/bedc-deep/supervisor.py` | `pipeline_status` | `ready_for_local_packet` | 55 | `awaiting_operator_acceptance` | summarize as review packet; Killo/golden required before paper write |

## Blocked Or Review-Only Inputs

| Source | Kind | Readiness | Score | Blocking reason |
| --- | --- | --- | ---: | --- |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/ComplexLimitUp/Constant.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/ComplexLimitUp/Difference.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/ComplexLimitUp/LinearClosure.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/ComplexLimitUp/NameCertificate.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/ComplexLimitUp/PointwiseNegation.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/ComplexLimitUp/SourceSpec.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/ComplexTopologyUp/Density.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/DyadicRatCoreUp/RealPhaseSourceCoverage.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/HilbertUp/LedgerExhaustion.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/HilbertUp/NameCertSurface.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/HilbertUp/ProjectionBridge.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/HilbertUp/StdBridge.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/PolynomialUp/Evaluation.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/RealAnalyticUp/CosEmpty.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/RealUp/CommonHeadCancel.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/RealUp/ConstantCarrierContext.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/RealUp/ConstantStream.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/RealUp/ConstantStreamBridge.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/RealUp/Core.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:lean4/BEDC/Derived/RealUp/DyadicRatCore.lean` | `lean_theorem` | `blocked_automath_not_ready` | 53 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/codex-auto-dev:lean4/BEDC/Derived/BeliefUp/TasteGate.lean` | `taste_gate_witness` | `needs_operator_review` | 52 | operator review is required before this can become receivable |
| `the-omega-institute/newmath@origin/codex-auto-dev:lean4/BEDC/Derived/PolicyUp/TasteGate.lean` | `taste_gate_witness` | `needs_operator_review` | 52 | operator review is required before this can become receivable |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/banach/intro_and_carrier.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/banach/singleton_certificate.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/commring/19_commring_zero_divisor_and_inclusion.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/complex_limit/01_distance_and_sequence.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/complex_limit/03_constant_and_difference_closure.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/hilbert/carrier_and_certificate.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/hilbert/orthogonal_projection_row.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/hilbert/orthogonal_residual_decomposition.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/hilbert/projection_and_geometry.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/innerproduct/public_namecert_export.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/measure/carrier_surface.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/measure/certificate_theorems.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/measure/relative_difference_rows.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/real/13_real_alg_order_interface.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/real/13_real_constant_core.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/real/13_real_constant_inner_endpoint_absurd.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/real/constant_tail_readback/01_classifier_tail_readback.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/real/constant_tail_readback/02_bridge_denominator_packages.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/real/constant_tail_readback/03_full_denominator_tail_packages.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/real/constant_tail_readback/04_obligation_boundary.tex` | `paper_claim` | `blocked_automath_not_ready` | 43 | Automath receiving theorem or article section has not been selected |
| `the-omega-institute/newmath@origin/codex-auto-dev:papers/bedc/parts/concrete_instances/269_belief_namecert_construction.tex` | `paper_seed_stub` | `needs_operator_review` | 30 | operator review is required before this can become receivable |
| `the-omega-institute/newmath@origin/codex-auto-dev:papers/bedc/parts/concrete_instances/270_policy_namecert_construction.tex` | `paper_seed_stub` | `needs_operator_review` | 30 | operator review is required before this can become receivable |

## Policy

- The selection gate admits only `ready_for_local_packet` records into the receivable table.
- `needs_operator_review` records a boundary, not acceptance, and is not selected for writeback.
- `blocked_automath_not_ready` means NewMath evidence exists but Automath has not chosen a receiving paper/Lean target; it is never selected as returnable content.
- The post-gate requires operator acceptance before any Killo/golden distillation candidate can be used.
- Automath paper writeback must pass the native Killo/golden distillation and review lane.
- BEDC text, seed stubs, and TasteGate witnesses must not be copied verbatim into Automath paper content.
