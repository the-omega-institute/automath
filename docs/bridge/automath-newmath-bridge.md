# Automath-NewMath bridge ledger

## Design intent

This ledger defines the first bridge layer between Automath and NewMath. The
goal is not automatic content transfer. The goal is a durable protocol that lets
humans and future AI agents answer:

- Which repo, branch, commit, and path did an item come from?
- Which repo, branch, and path may consume it?
- Why is it being bridged?
- Is it only observed, or has it been accepted or consumed?
- Does it require operator review, TasteGate evidence, or another audit?
- Could it trigger paper, Lean, docs, publication, or external-send effects?

The bridge now has paired worktree branches:

- Automath: `bridge/automath-newmath-consumption`
- NewMath: `bridge/newmath-automath-consumption`

Both branches use the same manifest schema and local-only runtime directories.
The durable manifest path is `tools/automath_newmath_bridge/bridge_manifest.jsonl`
in each repo. NewMath remains an observed source through explicit refs such as
`origin/auto-dev` and `origin/codex-auto-dev`; Automath remains an observed
source through `origin/dev` and the Automath bridge worktree.

The recurring bridge supervisor is:

`tools/automath_newmath_bridge/bridge_supervisor.py`

It periodically fetches Automath and NewMath refs, discovers new or changed
artifacts, synthesizes cross-repo readiness, runs bridge gates, and writes
local-only review packets when explicitly enabled. Runtime outputs are ignored
by Git and must not be uploaded.

## Current bridge directions

| Direction | Source artifacts | Candidate destination use | Status |
| --- | --- | --- | --- |
| NewMath to Automath | BEDC proposal prompts, accepted proposals, seed-stubs, TasteGate witnesses, BEDC audit rules | Automath autoresearch proposal queues, paper/writeback gates, and durable bridge records | observed |
| Automath to NewMath | Lean corpus inventory, paper claim targets, distillation lifecycle, dossier/publication slugs, audit failures | NewMath research-object source material, planning layer, and task generation candidates | candidate |
| Bidirectional | Bridge manifest schema, bridge ledger, commit convention | Shared protocol if NewMath later chooses to mirror the manifest | candidate |

## Source and destination table

| Source | Destination | Artifact mapping | Required boundary |
| --- | --- | --- | --- |
| `newmath@origin/auto-dev:papers/bedc/scripts/prompts/phase_propose.txt` | `automath@bridge/automath-newmath-consumption:tools/automath_newmath_bridge/bridge_manifest.jsonl` | `proposal` to `candidate_mechanism` | operator review, TasteGate, audit |
| `newmath@origin/auto-dev:papers/bedc/proposals/accepted/21bed2eb_belief.md` | `automath@bridge/automath-newmath-consumption:tools/automath_newmath_bridge/bridge_manifest.jsonl` | `accepted_proposal` to `review_packet` | operator review, TasteGate, audit |
| `newmath@origin/auto-dev:lean4/scripts/review_proposals.py` | `automath@bridge/automath-newmath-consumption:tools/automath_newmath_bridge/README.md` | `review_packet` to `pipeline_status` | operator review, audit |
| `newmath@origin/codex-auto-dev:papers/bedc/parts/concrete_instances/269_belief_namecert_construction.tex` | this ledger | `paper_seed_stub` to `scope_ledger` | operator review, TasteGate, audit |
| `newmath@origin/codex-auto-dev:lean4/scripts/bedc_ci.py` | this ledger | `audit_failure` to `scope_ledger` | operator review, TasteGate, audit |
| `newmath@origin/codex-auto-dev:lean4/BEDC/Derived/BeliefUp/TasteGate.lean` | this ledger | `taste_gate_witness` to `scope_ledger` | operator review, TasteGate, audit |
| `automath@origin/dev:tools/autoresearch/prepare.py` | `newmath@origin/auto-dev:tools/automath_newmath_bridge/bridge_manifest.jsonl` | `paper_claim` to `open_problem_target` | operator review, audit |
| `automath@origin/dev:lean4/scripts/omega_ci.py` | `newmath@origin/auto-dev:tools/automath_newmath_bridge/bridge_manifest.jsonl` | `audit_failure` to `pipeline_status` | operator review, audit |
| `automath@origin/dev:tools/distillation/lifecycle.py` | `newmath@origin/auto-dev:tools/automath_newmath_bridge/bridge_manifest.jsonl` | `writeback_packet` to `candidate_mechanism` | operator review, audit |
| `automath@origin/dev:tools/distillation/distill.py` | `newmath@origin/auto-dev:tools/automath_newmath_bridge/bridge_manifest.jsonl` | `writeback_packet` to `review_packet` | operator review, writeback gate, audit |
| `automath@origin/dev:tools/chatgpt-oracle/oracle_pipeline.py` | `newmath@origin/auto-dev:tools/automath_newmath_bridge/bridge_manifest.jsonl` | `pipeline_status` to `candidate_mechanism` | operator review, publication risk review, audit |
| `automath@origin/dev:lean4/Omega/Folding/KilloFoldResonancePerronIndependenceQ12_17.lean` | `newmath@origin/auto-dev:tools/automath_newmath_bridge/bridge_manifest.jsonl` | `lean_theorem` to `candidate_mechanism` | operator review, audit |
| `automath@origin/dev:lean4/Omega/Folding/KilloFoldResonanceDiscCharactersQ1217.lean` | `newmath@origin/auto-dev:tools/automath_newmath_bridge/bridge_manifest.jsonl` | `lean_theorem` to `candidate_mechanism` | operator review, audit |
| `automath@origin/dev:lean4/Omega/Folding/KilloFoldBinEscortRenyiLogisticGeometry.lean` | `newmath@origin/auto-dev:tools/automath_newmath_bridge/bridge_manifest.jsonl` | `lean_theorem` to `candidate_mechanism` | operator review, audit |
| `automath@origin/dev:lean4/Omega/Folding/KilloFoldBinNormalizedGaugeDeficiencyTailRigidity.lean` | `newmath@origin/auto-dev:tools/automath_newmath_bridge/bridge_manifest.jsonl` | `lean_theorem` to `candidate_mechanism` | operator review, audit |
| `automath@origin/dev:docs/dossier/index.qmd` | `newmath@origin/auto-dev:tools/automath_newmath_bridge/bridge_manifest.jsonl` | `publication_slug` to `publication_slug` | operator review, audit, publication risk review |
| `newmath@origin/auto-dev:tools/bedc-deep/supervisor.py` | paired bridge manifests | `pipeline_status` to `pipeline_status` | operator review, audit |
| `newmath@origin/auto-dev:lean4/BEDC/Derived/RealUp/*.lean` | `automath@bridge/automath-newmath-consumption:tools/automath_newmath_bridge/inbox/newmath/*.json` | `lean_theorem` to `candidate_mechanism` | operator review, TasteGate, audit, Automath receiving queue decision |
| `newmath@origin/auto-dev:papers/bedc/parts/concrete_instances/**/constant*.tex` | `automath@bridge/automath-newmath-consumption:tools/automath_newmath_bridge/inbox/newmath/*.json` | `paper_claim` to `candidate_mechanism` | operator review, TasteGate, audit, publication risk review |

## Accepted bridge rules

1. Every bridge item must have an explicit source repo, source ref, source path,
   source commit, destination repo, destination ref, and destination path.
2. `observed` and `candidate` records do not authorize content movement.
3. `accepted` requires operator review. A script may report candidates but may
   not mark them accepted without a human action recorded in the manifest.
4. `consumed` requires the destination path to exist or the consuming commit to
   be named in a follow-up record.
5. NewMath `\origin{ai}` chapters past seed closure require the BEDC TasteGate
   witness marker enforced by `lean4/scripts/bedc_ci.py`.
6. Automath writebacks remain governed by the distillation review gate and
   paper/Lean audits. The bridge manifest is not a writeback approval.
7. Outreach/open-problem runtime state remains separate. Bridge records may
   observe outreach patterns, but they must not write bridge state into
   `tools/community-outreach/outreach_state` or the active outreach board.
8. Public dossier or publication use has publication risk. It requires explicit
   operator approval before bridge status appears on public pages.
9. The supervisor may fetch latest refs from both repos, but it must not push.
10. Intermediate artifacts stay local-only under `inbox/`, `out/`, `state/`,
   and `logs/`.
11. Automatic writeback is limited to ignored local review packets. Durable
   paper / Lean / docs writes require accepted or consumed manifest records and
   the destination project's own gates.
12. Discovery is not readiness. The bridge must synthesize both repo contents
    before packet writes, especially for emergent NewMath constant material.
13. NewMath constant/RealConstant records are `blocked_automath_not_ready`
    until an operator chooses the receiving Automath queue and destination gate.

## Operator approval boundary

Bridge tooling may:

- scan configured source paths;
- fetch latest refs for configured repos;
- discover new or changed artifacts as both repos grow;
- read current Git refs and commits;
- generate local candidate packets;
- run deterministic bridge gates;
- write ignored local review packets after gates pass;
- validate JSONL records;
- render Markdown reports.

Bridge tooling may not:

- push to public branches;
- send email;
- post issues, comments, or social messages;
- submit papers;
- publish intermediate artifacts;
- merge `dev`, `auto-dev`, or integration branches;
- overwrite proposal or accepted proposal files;
- move source material into a durable destination without a manifest record;
- upload intermediate inbox/out/state/log artifacts to GitHub.

## TasteGate and audit boundary

NewMath BEDC has a concrete audit rule: if a chapter is marked `\origin{ai}`
and its theory closure is no longer `seedClosure`, the closure status must
reference `BEDC.Derived.<X>Up.taste_gate`. The Belief witness currently appears
as `BEDC.Derived.BeliefUp.taste_gate`.

Automath has a different audit surface: `omega_ci.py` tracks paper claim labels,
Lean registry labels, forbidden Lean constructs, and file verification. Its
distillation tooling adds writeback review and application planning. Bridge
records must name which audit applies instead of treating both projects as one
pipeline.

## Existing Automath code evidence

The bridge must reuse local Automath mechanisms where they already exist:

| Local code | Evidence | Bridge use |
| --- | --- | --- |
| `lean4/scripts/omega_ci.py` | `audit`, `inventory`, `search`, and `paper-coverage` commands over Lean declarations and paper labels | Find exact Lean theorem evidence and run zero-axiom/label gates before marking Automath artifacts consumed |
| `tools/distillation/distill.py` | `_validate_writebacks`, `_review_writebacks`, `SCORE_PASS_THRESHOLD = 7`, and `KILLO_GOLDEN_TRACE_RE` rejection of visible patch/log wording | Reuse Automath writeback gate for any paper writeback packet; do not invent a parallel bridge writeback path |
| `tools/chatgpt-oracle/oracle_pipeline.py` | staged F/A/B/C/D publication flow, `compile_gate`, audit gate events, and Stage D `/killo-golden` boundary | Treat publication-facing bridge use as medium-risk and operator-approved only |
| `lean4/Omega/Folding/KilloFoldResonancePerronIndependenceQ12_17.lean` | existing `paper_killo_fold_resonance_perron_independence_q12_17` theorem package | Candidate Automath-to-NewMath theorem evidence |
| `lean4/Omega/Folding/KilloFoldResonanceDiscCharactersQ1217.lean` | existing `paper_killo_fold_resonance_disc_characters_q12_17` theorem package | Candidate Automath-to-NewMath theorem evidence |
| `lean4/Omega/Folding/KilloFoldBinEscortRenyiLogisticGeometry.lean` | `killoEscortTheta`, KL/Renyi divergence, Fisher information on the golden escort logistic curve | Candidate golden mechanism evidence |
| `lean4/Omega/Folding/KilloFoldBinNormalizedGaugeDeficiencyTailRigidity.lean` | normalized gauge-deficiency tail rigidity and recovered even-zeta values | Candidate golden/Killo mechanism evidence |

This table is deliberately evidence-first. Future agents should add bridge
records by naming exact files and theorem labels found locally, not by
describing generic "Automath has gates" behavior.

## Supervisor and gate model

The bridge supervisor follows the same operational ideas as the local
distillation, NewMath BEDC supervisor, and loning/oracle pipelines:

| Existing pattern | Bridge equivalent |
| --- | --- |
| fixed branch guard | `--branch bridge/automath-newmath-consumption` |
| stop file | `tools/automath_newmath_bridge/.bridge_supervisor.stop` |
| fetch before pass | fetch Automath and NewMath configured refs |
| dashboard/log file | `tools/automath_newmath_bridge/logs/bridge_supervisor.log` |
| source queue / runtime state | ignored `inbox/`, `out/`, and `state/` |
| deterministic policy gate | `bridge_gates.py` |
| cross-repo readiness synthesis | `bridge_synthesis.py` |
| review packet before writeback | ignored `inbox/writeback_packets/*.json` |
| publication / review gates | no public-facing use without explicit approval |

The bridge synthesis layer scans both repos, not just refs:

- NewMath constant and `RealConstant*` Lean declarations under
  `lean4/BEDC/Derived/**/*.lean`;
- NewMath constant paper labels and `\leanchecked{...}` references under
  `papers/bedc/parts/concrete_instances/**/*.tex`;
- NewMath `tools/bedc-deep/supervisor.py` for low-water refill, loning watch,
  Stage 2 reject clusters, PI review, and guarded commit behavior;
- NewMath TasteGate witnesses under `lean4/BEDC/Derived/**/TasteGate.lean`;
- Automath Killo/golden Lean modules under `lean4/Omega/**`;
- Automath gate surfaces in `omega_ci.py`, `codex_formalize.py`,
  `tools/distillation`, and `tools/chatgpt-oracle/oracle_pipeline.py`.

Synthesis readiness values are intentionally conservative:

- `observe_only`: record source material only.
- `needs_operator_review`: a packet may be useful but a human must decide.
- `ready_for_local_packet`: deterministic gates may emit an ignored packet.
- `blocked_automath_not_ready`: NewMath evidence exists, but Automath has no
  selected receiving target or gate. This is the expected state for current
  NewMath constant emergence.
- `ready_for_durable_write`: reserved for future use after manifest acceptance,
  destination gate selection, and operator approval.

The bridge gate checks that a record is schema-valid, points only to safe local
review-packet destinations for automatic writes, preserves TasteGate language
when required, and blocks durable paper / Lean / docs / outreach-state writes.

Approved local packet writes are still only "needs operator review" packets.
They are not accepted or consumed manifest entries.

Run one supervised pass:

```bash
python3 tools/automath_newmath_bridge/bridge_supervisor.py --once
```

Run periodically:

```bash
python3 tools/automath_newmath_bridge/bridge_supervisor.py --poll-interval 300
```

Persist seen-state and emit local review packets:

```bash
python3 tools/automath_newmath_bridge/bridge_supervisor.py \
  --once \
  --update-state \
  --apply-writeback-packets
```

## Future AI commit analysis

Future agents should inspect commits touching this bridge by reading:

1. The commit message Source block.
2. The commit message Destination block.
3. `tools/automath_newmath_bridge/bridge_manifest.jsonl`.
4. Any generated packet under `tools/automath_newmath_bridge/out/`.
5. This ledger.

If a commit only changes schema, manifest, scripts, or reports, it should be
interpreted as protocol work unless a manifest line explicitly marks a bridge
item `accepted` or `consumed`.

## Commit message convention

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
  - docs/bridge/automath-newmath-bridge.md

Purpose:
- Establish an auditable bridge protocol before any automatic content movement.

Audit boundary:
- operator review required: yes
- TasteGate required: yes
- Lean build required: no
- external publication/send: no

AI-analysis note:
- This commit records source observation and bridge rules only. It does not
  accept, consume, publish, push, or synchronize content.
```

For Automath-to-NewMath commits, reverse the Source and Destination blocks and
keep the same audit-boundary fields.
