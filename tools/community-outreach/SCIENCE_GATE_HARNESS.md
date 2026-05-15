# Outreach Science Gate Harness

This file records the hard harness used by the outreach/openproblem pipeline.
It mirrors the BEDC/NewMath gate discipline in outreach terms: broad discovery
is allowed, but deep reasoning and writeback require explicit witnesses.

## Three Independent Axes

Every runnable target carries a `science_contract` in
`targets/<slug>/profile.json`. The contract reports three independent axes:

- `closure_status`: mathematical closure only.
  Values: `seed`, `scoped_target`, `partial_progress`, `scoped_closed`,
  `public_closed`.
- `verification_status`: evidence/audit status only.
  Values: `unverified`, `source_audited`, `artifact_present`, `reproducible`,
  `independently_judged`, `operator_approved`.
- `outreach_status`: display/send status only.
  Values: `not_drafted`, `draftable`, `draft_ready`, `approved`, `sent`,
  `archived`.

These axes must not be confused. A good email draft does not close the math.
Operator approval does not prove the theorem. A certificate does not authorize
external sending.

## Taste Obligations

AI/inbox/external-thread targets must provide four taste witnesses before RUN:

1. `novelty_witness`: why this is not stale, duplicate, or renamed work.
2. `no_hidden_assumption_witness`: what assumptions/sources are allowed and
   what is explicitly excluded.
3. `reproducibility_witness`: what artifact/check/certificate lets another
   reviewer audit the claim.
4. `layer_separation_witness`: how math evidence, Automath/NewMath relation,
   draft prose, and external send remain separate.

This is the outreach analogue of BEDC `TasteGate`: the target cannot write its
own trivial pass condition. The gate demands witnesses tied to the target.

## Lifecycle

The deterministic gate command is:

```bash
python3 tools/community-outreach/outreach_science_gate.py --audit
```

## Target Lanes

The contract also has a deterministic lane, either explicit in
`science_contract.target_lane` or inferred from `contribution_type`.

- `math_lane`: theorem, counterexample, construction, or research-note work.
  It must have a proof/theorem/counterexample/construction verifier.
- `frontier_lane`: computational record or certificate work. It must have a
  score/verifier/certificate route, preferably a `results.json` or frontier
  search artifact.
- `collaboration_lane`: email/thread collaboration packets. It must have an
  explicit ask, thread state, next-contact gate, and operator approval path.
- `audit_lane`: source-audit notes. It must preserve source/currentness risk
  and avoid presenting an audit as a theorem.

Broad discovery can fill the candidate inbox, but no target enters deep
reasoning unless its lane is known.

## Contract Quality

The harness computes `contract_quality` from deterministic text features. It is
not a truth oracle; it is a hallucination brake. The default floor is 7/10 and
can be raised with `science_contract.contract_quality_floor`.

Subscores:

- `novelty_score`: source/currentness/duplicate/staleness witness.
- `verifiability_score`: exact proof/check/certificate/audit condition.
- `progress_metric_score`: monotone metric a turn can actually lower.
- `artifact_score`: terminal artifact and expected outputs.
- `bridge_score`: Automath/NewMath/Omega relation, useful but not decisive.
- `surface_score`: writeback/close/operator-review surface.

If the score or any hard subscore is too weak, the target goes to
`NEEDS_CONTRACT` with `next_action=profile_judge`. This is intentional: weak
contracts should be repaired before reasoning, not after several empty turns.

Per-target statuses:

- `BOARD_SKIPPED`: board says closed, overtaken, handoff, drop, submitted, or
  pending user approval.
- `NEEDS_CONTRACT`: profile or science contract/taste obligations are missing.
- `NEEDS_EVIDENCE`: contract is present but evidence does not yet satisfy the
  verifier.
- `CONTRACT_READY`: contract is clean; target may be deep-reasoned when
  preflight says RUN. Freshness/currentness warnings are risk flags unless the
  target profile explicitly makes them part of the mathematical verifier.
- `WRITEBACK_READY`: verifier/evidence supports an operator-reviewed draft or
  paper packet.
- `CLOSE_TARGET`: target should be archived, dropped, or re-scoped.

`next_action` is derived from status:

- `profile_judge` for missing contracts.
- `deep_reason` for evidence gaps.
- `operator_review` for writeback-ready artifacts.
- `operator_archive_review` for closure/drop decisions.
- `skip` for board-skipped rows.

## Writeback Rule

Writeback is allowed only when the science gate reaches `WRITEBACK_READY`.
The pipeline may generate drafts, notes, and paper packets automatically, but
external sending remains user-gated.

For `collaboration_lane`, writeback means an operator-reviewable reply packet,
specific ask, or collaboration plan. It never upgrades mathematical
`closure_status`. For `math_lane` and `frontier_lane`, writeback requires proof,
construction, counterexample, reproducible certificate, or a clearly scoped
audit/failure note.

## No-Progress Rule

Deep reasoning must lower the contract's `progress_metric`. If repeated turns
add no new lemma, calculation, construction, certificate, obstruction, or
source correction, the oracle loop stops as `STUCK` according to
`no_progress_patience_turns`.
