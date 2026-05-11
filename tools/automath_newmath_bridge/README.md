# Automath-NewMath bridge

This directory defines the first-stage bridge layer between
`the-omega-institute/automath` and `the-omega-institute/newmath`.

The bridge is intentionally gated. It records source artifacts, candidate
destinations, review boundaries, and audit obligations. The supervisor may
fetch the latest refs and generate local review packets, but it does not push,
publish, send external messages, or directly write paper / Lean / dossier
content.

## Files

- `bridge_manifest.schema.json` defines the JSONL record contract.
- `bridge_manifest.jsonl` is the durable manifest. Each line is one auditable
  source-to-destination record.
- `bridge_sources.json` is the read-only scan configuration used to generate
  candidate packet records.
- `scan_bridge_sources.py` observes configured paths and writes candidate JSONL.
- `bridge_pipeline_config.json` defines dynamic discovery rules for growing
  Automath and NewMath refs.
- `run_bridge_pipeline.py` discovers new or changed bridgeable artifacts from
  both repos, compares blob-level seen state, computes priority scores,
  synthesizes cross-repo readiness, renders a local transfer plan, and writes
  an ignored top-K agent queue.
- `bridge_synthesis.py` scans both repos for matching evidence: NewMath
  constant/RealConstant material, BEDC TasteGate/supervisor patterns, Automath
  Killo/golden Lean surfaces, and Automath gate surfaces.
- `bridge_gates.py` runs deterministic local gates over the bridge inbox.
- `bridge_supervisor.py` periodically fetches both repos, runs discovery, runs
  gates, and can write local ignored review packets.
- `bridge_heavy_loop.py` runs slow synthesis and Automath writeback dry-runs on
  an isolated cadence so the main scanner can keep polling.
- `bridge_production_loop.py` turns eligible NewMath-to-Automath synthesis
  output into lightweight durable Automath receiving indexes without writing
  Automath paper or Lean content.
- `bridge_watchdog.py` supervises persistent supervisor/heavy/production-loop
  health without joining any work queue.
- `bridge_to_automath_killo_golden.py` converts accepted NewMath-to-Automath
  bridge records into Automath distillation candidates and invokes the existing
  Killo/golden Claude writeback lane when explicitly requested.
- `validate_bridge_manifest.py` validates manifest or packet JSONL records.
- `render_bridge_report.py` renders manifest or packet JSONL as Markdown for
  human and AI review.
- `inbox/`, `out/`, `state/`, and `logs/` are runtime directories. Generated
  contents are ignored by Git and should not be uploaded.
- Generated review-packet JSON files are also ignored. Durable bridge decisions
  belong in commit messages, `bridge_manifest.jsonl`, and native receiving
  artifacts, not in intermediate packet files.

The bridge ledger lives at `docs/bridge/automath-newmath-bridge.md`.

## Loop separation

The bridge uses four independent loops:

- `bridge_supervisor.py` is the main scanner. It fetches configured refs,
  updates ignored seen-state, refreshes the agent queue, and runs deterministic
  gates.
- `bridge_heavy_loop.py` handles slower synthesis and Automath writeback
  dry-runs from already generated artifacts. Restarting or changing it must not
  interrupt the main scanner.
- `bridge_production_loop.py` converts NewMath-to-Automath output into durable
  receiving indexes while preserving the Killo/golden writeback boundary for
  paper content. Synthesis-only rows are review leads, not deterministic gate
  passes.
- `bridge_watchdog.py` checks that the other loops remain healthy. It writes
  only ignored status/log files and can optionally push the current `codex/*`
  audit branch when it is clean and ahead of its upstream.

Each loop has its own stop file:

```text
tools/automath_newmath_bridge/.bridge_supervisor.stop
tools/automath_newmath_bridge/.bridge_heavy_loop.stop
tools/automath_newmath_bridge/.bridge_production_loop.stop
tools/automath_newmath_bridge/.bridge_watchdog.stop
```

The watchdog's ignored outputs are:

```text
tools/automath_newmath_bridge/logs/bridge_watchdog.log
tools/automath_newmath_bridge/state/bridge_watchdog_status.json
```

One health pass:

```bash
python3 tools/automath_newmath_bridge/bridge_watchdog.py --once
```

Persistent watchdog:

```bash
python3 tools/automath_newmath_bridge/bridge_watchdog.py \
  --poll-interval 900
```

Production loop:

```bash
python3 tools/automath_newmath_bridge/bridge_production_loop.py \
  --poll-interval 1800 \
  --push
```

Safe branch push is opt-in and restricted to the current clean `codex/*` audit
branch:

```bash
python3 tools/automath_newmath_bridge/bridge_watchdog.py \
  --poll-interval 900 \
  --push-safe-current-branch
```

The watchdog does not create PRs, merge BEDC branches, push production bridge
branches, or commit runtime artifacts.

Only records with `gate_status=gate_passed` may enter Automath-native
Killo/golden writeback. `Input source: synthesis` in a receiving index is an AI
review signal, not permission to write paper or Lean content.

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

## Supervisor pipeline

The growth-aware supervisor is the intended recurring entry point:

```bash
python3 tools/automath_newmath_bridge/bridge_supervisor.py --once
```

One pass does this:

1. Verifies the current branch is `bridge/automath-newmath-consumption`.
2. Fetches latest refs for Automath and NewMath unless `--no-fetch` is passed.
3. Discovers new or changed artifacts from both repos.
4. Synthesizes readiness from both repo contents.
5. Writes a local inbox, synthesis report, and transfer plan.
6. Runs deterministic gates.
7. Dry-runs the Automath-native Killo/golden writeback adapter, or applies it
   with `--apply-automath-writeback`.
8. Optionally writes local review packets if `--apply-writeback-packets` is
   passed.

Continuous mode:

```bash
python3 tools/automath_newmath_bridge/bridge_supervisor.py \
  --poll-interval 300
```

Stop continuous mode by creating:

```text
tools/automath_newmath_bridge/.bridge_supervisor.stop
```

The supervisor follows the local distillation/oracle pattern:

- fixed branch guard;
- stop file;
- fetch before each pass;
- dry local runtime artifacts;
- deterministic gates before local packet writes;
- Automath paper writes only through `tools/distillation/supervisor.py`;
- optional push is limited to `bridge/automath-newmath-consumption`;
- no external send;
- no direct Lean / docs / outreach-state writes.

Local runtime outputs:

- `tools/automath_newmath_bridge/inbox/bridge_inbox.jsonl`
- `tools/automath_newmath_bridge/inbox/writeback_packets/*.json`
- `tools/automath_newmath_bridge/out/bridge_agent_queue.jsonl`
- `tools/automath_newmath_bridge/out/bridge_transfer_plan.md`
- `tools/automath_newmath_bridge/out/bridge_synthesis_report.md`
- `tools/automath_newmath_bridge/out/bridge_synthesis.jsonl`
- `tools/automath_newmath_bridge/out/bridge_gate_results.jsonl`
- `tools/automath_newmath_bridge/state/bridge_state.json`
- `tools/automath_newmath_bridge/state/bridge_events.jsonl`
- `tools/automath_newmath_bridge/logs/bridge_supervisor.log`

Those files are intentionally ignored. Durable project decisions belong in
`bridge_manifest.jsonl`, not in runtime artifacts.

Generated review packet JSON files are intermediate artifacts too. If a review
packet becomes a durable source for an Automath decision, summarize it in the
commit message and record the accepted decision in the manifest or native
Automath writeback artifact rather than committing the packet itself.

The runner records scan discipline in ignored state:

- `artifact_key` identifies a source repo/ref/path.
- `source_blob` records the Git blob hash for content-level seen checks.
- `candidate_hash` identifies the emitted bridge candidate.
- `priority_score` combines rule priority, change kind, artifact kind, risk,
  TasteGate requirements, and prior attempts.
- `cooldown_until`, `rejected`, `blocked`, and `consumed` state entries suppress
  unchanged content until the blob changes or cooldown expires.
- `bridge_events.jsonl` appends ignored event records when `--update-state` is
  used.

LLM agents should consume `out/bridge_agent_queue.jsonl`, not rescan the whole
repository. Queue entries list allowed actions and explicitly forbid durable
writes, acceptance, or push.

To persist "already seen" local state:

```bash
python3 tools/automath_newmath_bridge/bridge_supervisor.py --once --update-state
```

To write local review packets for gate-passed candidates:

```bash
python3 tools/automath_newmath_bridge/bridge_supervisor.py \
  --once \
  --update-state \
  --apply-writeback-packets
```

These packets are review material only. They do not authorize destination
writes.

To allow accepted NewMath-to-Automath bridge records to enter the Automath
paper lane:

```bash
python3 tools/automath_newmath_bridge/bridge_supervisor.py \
  --once \
  --apply-automath-writeback \
  --push-branch
```

The adapter only considers NewMath-to-Automath records whose bridge status is
already `accepted` or `consumed`; current `blocked_automath_not_ready` NewMath
constant records are ignored. The paper writeback itself is owned by
`tools/distillation/supervisor.py`, which uses the existing Killo/golden style
checks and Claude review gate. `--push-branch` pushes only
`bridge/automath-newmath-consumption` after that native lane succeeds.

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

Run deterministic gates directly:

```bash
python3 tools/automath_newmath_bridge/bridge_gates.py \
  tools/automath_newmath_bridge/inbox/bridge_inbox.jsonl \
  --output tools/automath_newmath_bridge/out/bridge_gate_results.jsonl
```

Run synthesis directly after an inbox exists:

```bash
python3 tools/automath_newmath_bridge/bridge_synthesis.py \
  --config tools/automath_newmath_bridge/bridge_pipeline_config.json \
  --input tools/automath_newmath_bridge/inbox/bridge_inbox.jsonl \
  --output tools/automath_newmath_bridge/out/bridge_synthesis.jsonl
```

NewMath constants are intentionally treated as source evidence until an
operator chooses a receiving Automath queue and audit boundary. The synthesis
layer can mark these records `blocked_automath_not_ready`; that is a useful
decision, not a failure.

## Selection Gates

NewMath-to-Automath intake uses two gates:

- The selection gate admits only `ready_for_local_packet` records into the
  receivable index. `blocked_automath_not_ready`, `observe_only`, and
  `needs_operator_review` records are kept in the blocked/review-only table and
  are not treated as returnable content.
- The post-polish gate requires operator acceptance before a record may become
  a Killo/golden distillation candidate. The distillation lane must still pass
  Automath style validation, Claude review, writeback validation, and any local
  paper checks before content can become durable paper text.

`blocked_automath_not_ready` means that NewMath evidence has been detected, but
Automath has not selected a receiving theorem, article section, paper label, or
Lean target. The bridge may record the block and priority, but it must not
select that item as writable content.

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

Runtime artifacts excluded from git:
- tools/automath_newmath_bridge/inbox/**
- tools/automath_newmath_bridge/out/**
- tools/automath_newmath_bridge/state/**
- tools/automath_newmath_bridge/logs/**
- tools/automath_newmath_bridge/review_packets/*.json

Gates:
- <command>: <passed/failed/skipped and reason>

Follow-up:
- <remaining risk, if any>

AI-analysis note:
- Future agents should infer that this commit records protocol and candidate
  observation only; it does not accept, consume, publish, or synchronize content.
```

For `automath_to_newmath` commits, reverse the Source and Destination blocks.

Every bridge commit should include enough provenance to reconstruct the work
without committing runtime artifacts. Do not commit generated inbox, out, state,
log, or review-packet JSON files. They may be regenerated from the committed
config, manifest, source refs, and commit message trail.
