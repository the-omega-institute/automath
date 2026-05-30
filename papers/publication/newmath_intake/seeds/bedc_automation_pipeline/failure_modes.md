# Failure Modes: BEDC Automation Pipeline

The paper should use failure modes as the main evidence that the architecture is
not a loose collection of agents.  Each failure mode below is a candidate table
row for a promoted manuscript.

| Failure mode | Where it appears | Detector | Why it matters | Permitted response |
|---|---|---|---|---|
| Paper marker names a missing Lean declaration | BEDC paper parts with Lean-marker macros | `bedc_ci.py marker-existence-audit` | A manuscript could otherwise present a formal-looking target that does not exist | Fix the marker, add the missing declaration in `newmath`, or downgrade the claim |
| Transitive axiom leakage | Lean declarations used as verified evidence | `bedc_ci.py axiom-purity --strict` and `tools/check-axioms.py` | A compiled theorem may still depend on an unacceptable axiom path | Block verified-status claims until the dependency surface is clean |
| Parameter-echo theorem growth | New Lean theorem signatures | `phase_d_lint.py` | Agents can add formally true but shallow statements that merely echo hypotheses | Reject the round and ask for a concrete BEDC kernel anchor |
| Missing BEDC anchor | New `BEDC.Derived.*` declarations | `phase_d_lint.py` | A declaration can compile while being detached from the intended kernel objects | Require a `BHist`, `BMark`, relation, signature, or NameCert anchor |
| Duplicate or shallow conclusion | Added theorem blocks in a worker branch | `phase_d_lint.py --include-shallow` | Rephrased theorems inflate counts without adding proof surface | Reject the change and route to theorem-deepening |
| Drift between paper labels and source paths | Publication manuscripts and source maps | `bedc_ci.py inventory`, automath source-map discipline | Reviewers cannot verify which source fact supports which claim | Refresh `SOURCE_MAP.md`/theorem inventory before manuscript assembly |
| Random candidate selection | Large backlog of formalization or paper tracks | `critical_path.py` scoring and dispatch windows | Parallel agents can converge on easy or duplicated tasks | Use critical-path scores and active-claim locks |
| Unreviewed LLM output | Agent-generated proofs, summaries, or review packets | Auto-AI quality packet layer | LLM text may be persuasive but non-load-bearing | Treat LLM output as advisory until deterministic gates and human review pass |
| Seed accidentally becomes active paper | Intake directories under automath | `pipeline_auto.py` active-paper conventions | A seed could be rewritten or submitted before promotion | Keep no `main.tex`, no `PIPELINE.md`, and no `2026_*` directory until human promotion |
| Publication-stage metadata gap | Active paper after promotion | `pub_check.py` | A technically strong manuscript can fail submission readiness | Block P7 until citation, style, proof, metadata, and pipeline checks pass |

## Minimum Case Studies Before Promotion

The promoted paper should include three to six concrete cases.  Each case must
name:

1. the track or source component;
2. the gate that found the issue;
3. the failure class;
4. the corrective action;
5. whether the correction was deterministic, agent-assisted, or human-reviewed.

Acceptable case-study families include marker drift, axiom-purity failures,
parameter echo, shallow theorem growth, source-map correction, overlap blocking,
and publication-stage submission-pack failures.
