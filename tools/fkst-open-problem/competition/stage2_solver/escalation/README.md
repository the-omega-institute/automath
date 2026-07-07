# SAIR-EQT2 Escalation Artifact

## What this is

A proof-carrying verifier-in-the-loop escalation artifact for SAIR-EQT2. It records an FKST-style Codex/Lean-judge loop that converts deterministic-solver residuals into machine-checked Lean certificates. It contains harness scripts, certificate JSONL files, replay manifests, and result ledgers for guided upper-bound and blind proof-carrying runs.

## What this is not

This is not a hosted leaderboard submission.
This is not a claim of new mathematics.
This is not a full blind benchmark yet.
Guided results are upper bounds.

## Results

| mode | verdict given? | scope | accepted | wrong accepted | status |
|---|---|---|---|---|---|
| deterministic solo | no LLM | sample_200 | 160/200 | - | baseline |
| deterministic solo | no LLM | hard2 | 65/200 | - | baseline |
| guided escalation | yes | 175 residuals | 173/175 | 0 | upper bound |
| blind (full) | no | 175 residuals | 174/175 | 0 | full run |

Guided totals after escalation are `sample_200` 200/200 and `hard2` 198/200 (residual misses `hard2_0027`, `hard2_0051`). Blind totals (verdict self-decided, judge as solve-time oracle) are `sample_200` 200/200 and `hard2` 199/200; the single blind residual miss is `hard2_0176`. Blind ≈ guided here because the counterexample/proof search itself reveals the verdict. All certificates are machine-checked with 0 wrong verdicts.

## Artifact layout

- `scripts/` contains the guided runner, blind runner, one-certificate verifier, manifest exporter, certificate schema checker, and result summarizer.
- `prompts/` contains the guided and blind Codex instructions used by the runs.
- `certs/` contains accepted certificate JSONL ledgers.
- `results/` contains result ledgers and `summary.md`.
- `manifests/` contains judge snapshot metadata and replay manifests.
- `docs/` contains the honest boundary, replay guide, internal memo, outline, and next steps.
- `data/residual_sets/` contains deterministic residual id lists derived from `results/guided_final_sweep.json`.
- `external/` documents the non-vendored judge dependency.

## Reproducing certificate verification

Clone the official judge separately and pin it to the snapshot recorded in `manifests/judge_snapshot.json`. The judge is not vendored here.

```sh
git clone https://github.com/SAIRcompetition/equational-theories-lean-stage2 /path/eqt2-stage2
cd /path/eqt2-stage2
git checkout 6805e2323018fbd8a85f41ca09fc33d74d5a02a5
```

Validate the local certificate ledgers:

```sh
python3 scripts/check_cert_jsonl.py certs/guided_certs.jsonl
python3 scripts/check_cert_jsonl.py certs/blind_spike_certs.jsonl
```

Replay of a specific certificate should use `scripts/verify_one.py --judge-root /path/eqt2-stage2 <problem.json> <answer.json>` and the rows in `manifests/certificate_replay_manifest.jsonl`.

## Running new escalation jobs

Guided escalation is parameterized:

```sh
python scripts/run_guided_escalation.py --judge-root /path/eqt2-stage2 --work-dir /path/scratch/guided --results-ref data/residual_sets --parallel 5 --timeout 1500
```

Blind escalation uses the same contract:

```sh
python scripts/run_blind_escalation.py --judge-root /path/eqt2-stage2 --work-dir /path/scratch/blind --results-ref data/residual_sets --parallel 5 --timeout 1500
```

Both runners depend on the Codex CLI and the local judge environment. They are resumable through scratch-directory cache files.

## Relation to FKST

The artifact follows the FKST discipline: extract the deterministic frontier, condition synthesis on problem statements and judge policy, ask Codex for Lean proofs or finite countermodels, and trust only certificates replayed by the Lean judge.

## Relation to router-hypothesis work

Earlier router-hypothesis work studies proof-routing over Lean-verified algebra under blind and cue-conditioned settings. This artifact is the constructive counterpart: a routes-and-proves escalation loop in the magma/equational SAIR-EQT2 domain.

## Honest boundary

See [docs/HONEST_BOUNDARY.md](docs/HONEST_BOUNDARY.md).
