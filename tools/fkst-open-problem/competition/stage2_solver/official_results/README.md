# Official runner result JSONs

These are raw outputs of the **official** `pipeline.runner` (full `DEFAULT_PROOF_POLICY`,
including `allowed_declarations`) from the upstream judge
`SAIRcompetition/equational-theories-lean-stage2`, run locally with
`PYTHONDONTWRITEBYTECODE=1`. They are the authoritative score evidence — NOT the local
`measure_b.py` harness (which omitted `allowed_declarations` and produced inflated false
positives; see `../SUBSTRATE_NOTES.md`).

## Which file is the truth

| file | set | solved | status |
|---|---|---|---|
| `sample200_final.json` | sample_200 | **160 / 200** | **CURRENT** (fixed solver) |
| `hard2_final.json` / `hard2_recheck.json` | hard2 | **65 / 200** | **CURRENT** (fixed solver) |

Broken intermediate official-runner snapshots are preserved for audit under
`superseded/`, so the non-authoritative byte evidence remains on disk with explicit
labels.

Only the authoritative `*_final` (and `hard2_recheck`) snapshots are committed here. The
intermediate broken-version snapshots are kept under `superseded/` with reason-coded
filenames but are **not** authoritative — the full regression-and-fix story is written up
in `../SUBSTRATE_NOTES.md`.

## How they were produced

```bash
cd /tmp/eqt2-stage2 && source .env.judge
rm -rf <submission>/__pycache__            # runner rejects a submission dir with extras
rm -f pipeline/results/<out>.json
PYTHONDONTWRITEBYTECODE=1 python3 -m pipeline.runner \
  --submission <abs-path>/submission --problems examples/problems/<file> \
  --output pipeline/results/<out>.json
```

## Provenance gap (honest note)

The local judge clone at `/tmp/eqt2-stage2` was **purged by macOS's 3-day `/tmp` cleanup**
after these runs, so the exact judge commit SHA is **no longer retrievable** and these
numbers **cannot currently be re-derived locally** without re-cloning + rebuilding the judge
(`scripts/setup.sh`). The JSONs here are the last official run's byte output; treat them as
trust-on-disclosure, re-run-required before any external quote. `sample_20`, `hard1`,
`hard3` were not re-verified on the fixed solver before the purge — their current numbers
are unknown; do not quote the old `measure_b.py` figures for them.
