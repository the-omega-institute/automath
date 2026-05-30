# Artifact Inventory: BEDC Rule 110 Finite Witness Artifacts

The counts below are intake claims from `rule110/STATUS.md` at source commit
`3fb3d6a0641767388a401883062aa522ea0b397b`. They must be rechecked before
submission.

## Reported Artifact Counts

| Item | Count / status |
|---|---:|
| Test binaries | 50 |
| C LOC across evaluator, encoder, tests | 20167 |
| Lean LOC across `lean4/BEDC/FKernel` | 4723 |
| Source `.enum.ct` manifests | 37 |
| Source `.algo.ct` manifests | 22 |
| Generated `.r110.ct` manifests | 59 |
| Generated `.algo.r110.ct` manifests | 22 |
| Total `.ct` files after `make test` materialization | 118 |
| FKernel / GroundCompiler semantic cases | 470 |
| Martinez phase verifier entries | 177 |
| Martinez collision rows cross-checked | 33 |
| Cook packet scale frontier | `scale_2p_16t_16384` |

## Required Rechecks Before Promotion

- Confirm `make clean && make && make test` exits 0 on the source commit.
- Recompute manifest counts from the filesystem.
- Decide whether `make test-collision-audit` is a paper gate or a diagnostic
  limitation, because `STATUS.md` records a strict table audit with failures.
- Separate finite-witness claims from Cook phase-exact universality claims in
  the abstract.

