# Automath-NewMath bridge

This directory defines the first-stage bridge layer between
`the-omega-institute/automath` and `the-omega-institute/newmath`.

The bridge is intentionally conservative. It records source artifacts,
candidate destinations, review boundaries, and audit obligations. It does not
sync files, accept proposals, apply writebacks, publish artifacts, push
branches, or send external messages.

## Files

- `bridge_manifest.schema.json` defines the JSONL record contract.
- `bridge_manifest.jsonl` is the durable manifest. Each line is one auditable
  source-to-destination record.
- `bridge_sources.json` is the read-only scan configuration used to generate
  candidate packet records.
- `scan_bridge_sources.py` observes configured paths and writes candidate JSONL.
- `validate_bridge_manifest.py` validates manifest or packet JSONL records.
- `render_bridge_report.py` renders manifest or packet JSONL as Markdown for
  human and AI review.

The bridge ledger lives at `docs/bridge/automath-newmath-bridge.md`.

## Artifact kinds

The manifest schema currently admits these bridge artifact kinds:

- `proposal`
- `accepted_proposal`
- `paper_seed_stub`
- `taste_gate_witness`
- `lean_theorem`
- `paper_claim`
- `open_problem_target`
- `scope_ledger`
- `review_packet`
- `writeback_packet`
- `publication_slug`
- `pipeline_status`
- `audit_failure`
- `candidate_mechanism`

## Status meanings

- `observed`: recorded as source material, not yet approved for consumption.
- `candidate`: plausible bridge item awaiting operator decision.
- `accepted`: approved by an operator for the named destination.
- `consumed`: destination has used the artifact and recorded the resulting path.
- `blocked`: cannot move forward without a specific fix.
- `needs_operator_review`: explicitly awaiting human approval.

## Required fields

Every bridge manifest record must include source and destination fields:

- `source_repo`
- `source_branch_or_ref`
- `source_path`
- `source_commit`
- `source_artifact_kind`
- `destination_repo`
- `destination_branch_or_ref`
- `destination_path`
- `destination_artifact_kind`
- `bridge_direction`
- `status`
- `operator_review_required`
- `taste_gate_required`
- `audit_required`
- `notes`
- `next_action`

The bridge direction is one of:

- `newmath_to_automath`
- `automath_to_newmath`
- `bidirectional`

## Review and audit boundary

NewMath BEDC proposal material has a strict lifecycle:

1. AI proposes one chapter.
2. Operator review accepts or rejects.
3. Acceptance may create a paper seed-stub with `\origin{ai}`.
4. Audit blocks any AI-origin chapter from leaving seed closure unless the
   closure status cites the relevant `BEDC.Derived.<X>Up.taste_gate` witness.

Automath has analogous gates around paper claim labels, Lean registry coverage,
distillation writeback review, and outreach/open-problem state. Bridge records
may refer to those systems, but this bridge layer does not write into their
runtime state.

## Local Automath evidence to reuse

Bridge consumers should prefer these existing Automath mechanisms before adding
new glue:

- `lean4/scripts/omega_ci.py audit` is the local zero-axiom and label-integrity
  gate. It scans Lean files for `sorry`, `admit`, raw `axiom`, and orphan
  paper-label doc blocks.
- `lean4/scripts/omega_ci.py inventory` and `search` are the local declaration
  retrieval path for exact Lean modules and paper labels.
- `tools/distillation/distill.py` already validates writeback packets, rejects
  visible pipeline metadata, rejects visible `/killo-golden` patch/log wording
  in paper LaTeX, and uses a configured writeback review gate.
- `tools/chatgpt-oracle/oracle_pipeline.py` already defines the staged
  publication gate model, including compile repair and audit-gate events.
- Killo/golden Lean evidence already exists under `lean4/Omega/Folding/`, for
  example Perron independence, discriminant-character obstructions, golden
  escort geometry, and normalized gauge-deficiency tail rigidity.

Future bridge records that mention Automath theorem evidence should cite exact
Lean module paths and, where available, exact `paper_*` labels.

## Commands

Generate a read-only candidate packet:

```bash
python3 tools/automath_newmath_bridge/scan_bridge_sources.py \
  --config tools/automath_newmath_bridge/bridge_sources.json \
  --output tools/automath_newmath_bridge/out/bridge_candidates.jsonl
```

Validate the durable manifest:

```bash
python3 tools/automath_newmath_bridge/validate_bridge_manifest.py \
  tools/automath_newmath_bridge/bridge_manifest.jsonl
```

Validate generated candidates:

```bash
python3 tools/automath_newmath_bridge/validate_bridge_manifest.py \
  tools/automath_newmath_bridge/out/bridge_candidates.jsonl
```

Render a review report:

```bash
python3 tools/automath_newmath_bridge/render_bridge_report.py \
  tools/automath_newmath_bridge/out/bridge_candidates.jsonl \
  --output tools/automath_newmath_bridge/out/bridge_report.md
```

## Commit message convention

Use commits that make the source-to-destination movement explicit:

```text
bridge(<direction>): <short action>

Source:
- repo: the-omega-institute/newmath
- ref: origin/auto-dev
- paths:
  - papers/bedc/scripts/prompts/phase_propose.txt
  - lean4/scripts/review_proposals.py
  - lean4/scripts/bedc_ci.py

Destination:
- repo: the-omega-institute/automath
- ref: bridge/automath-newmath-consumption
- paths:
  - tools/automath_newmath_bridge/...
  - docs/bridge/...

Purpose:
- Establish an auditable bridge protocol before any automatic content movement.

Audit boundary:
- operator review required: yes
- TasteGate required: yes
- Lean build required: no
- external publication/send: no

AI-analysis note:
- Future agents should infer that this commit records protocol and candidate
  observation only; it does not accept, consume, publish, or synchronize content.
```

For `automath_to_newmath` commits, reverse the Source and Destination blocks.
