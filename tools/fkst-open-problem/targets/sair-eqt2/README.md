# SAIR-EQT2 Focused Pipeline

This is the focused FKST automation surface for one external item:

```text
SAIR Equational Theories Stage 2
```

## Repository Decision

Keep this work inside `automath-outreach`.

Reason: the current FKST branch already contains the SAIR-EQT2 claim-state
artifact, the FKST package skeleton, and the Lean/checker references needed to
audit the certificate-layer claim. Creating a new repository now would duplicate
the source anchors and add synchronization risk without creating a better
mathematical audit boundary.

This directory is the boundary that keeps the work target-specific.

## Pipeline

Single target:

- `SAIR-EQT2`

Single durable output:

- `tools/fkst-open-problem/artifacts/sair-eqt2/claim_state.jsonl`

Single dry-run entry point:

```sh
python3 tools/fkst-open-problem/scripts/sair_eqt2_dry_run.py
```

The dry run:

- reads `tools/fkst-open-problem/targets/sair-eqt2/pipeline.json`;
- verifies that GitHub write automation is disabled;
- verifies Lean and checker-script references exist;
- generates the SAIR-EQT2 claim-state artifact into a temporary directory;
- compares the generated artifact byte-for-byte with the committed
  `claim_state.jsonl`.

To write the generated artifact to an explicit path while still comparing it:

```sh
python3 tools/fkst-open-problem/scripts/sair_eqt2_dry_run.py \
  --output /tmp/sair-eqt2-claim_state.jsonl
```

To inspect generation without comparing to the committed artifact:

```sh
python3 tools/fkst-open-problem/scripts/sair_eqt2_dry_run.py --no-compare
```

## Boundaries

This pipeline must not include:

- Israel collaboration work;
- Tolmetes collaboration work;
- T-43, T-44, T-32, or other previous open-ended Automath open-problem routes;
- a general automation framework;
- GitHub write automation without explicit approval;
- any claim that FKST consensus proves mathematics.

FKST consensus is routing state only. Mathematical truth must come from Lean,
checker/source-replay artifacts, or committed git artifacts.

## Current Claim Surface

The committed claim-state says only that Omega/Automath has a deterministic
certificate-layer contribution for SAIR Stage 2 participation. It does not claim
that the general Equational Theories project is solved, and it does not claim a
new theorem beyond the cited Lean anchors.
