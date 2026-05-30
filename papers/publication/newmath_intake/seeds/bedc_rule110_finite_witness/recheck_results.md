# Recheck Results: BEDC Rule 110 Finite Witness Artifacts

This is an intake-level recheck note, not a promoted artifact appendix.

- recheck date: 2026-05-31
- source repo: `D:/omega/newmath`
- source ref: `origin/dev`
- source commit: `3fb3d6a0641767388a401883062aa522ea0b397b`
- local workspace branch observed: `auto-dev`

## Execution Environment

The full dynamic artifact suite could not be run on this machine because
`make` is not installed or not on `PATH`:

```text
Get-Command make
The term 'make' is not recognized as the name of a cmdlet, function, script file, or operable program.
```

Therefore this note records only static source-tree counts and source-text
consistency checks.  The dynamic commands in `recheck_plan.md` remain required
before promotion:

```powershell
make clean
make
make test
make test-collision-audit
make test-scale
```

## Static Counts From the Pinned Git Tree

The counts below were recomputed from `origin/dev`, not from generated build
outputs.

| Count family | Rechecked value | Previously recorded value | Status |
|---|---:|---:|---|
| `tests/test_*.c` top-level test binaries | 56 | 50 | drift |
| top-level C LOC across `evaluator/*.c`, `encoder/*.c`, `tests/*.c` | 23914 | 20167 | drift |
| top-level Lean LOC across `lean4/BEDC/FKernel/*.lean` | 4723 | 4723 | matches |
| source `.enum.ct` manifests | 37 | 37 | matches |
| source `.algo.ct` manifests | 22 | 22 | matches |
| generated non-algorithm `.r110.ct` manifests in static git tree | 0 | 59 generated after materialization | not materialized |
| generated `.algo.r110.ct` manifests in static git tree | 0 | 22 generated after materialization | not materialized |
| total `.ct` files in static git tree | 59 | 118 after materialization | not materialized |

The local filesystem currently also shows only the 59 source `.ct` manifests
under `rule110/manifests`; generated Rule 110 manifests were not materialized
because `make test` could not be run.

## STATUS.md Consistency Issue

The pinned `rule110/STATUS.md` contains two statements that cannot both be
used unqualified in a promoted manuscript:

- the test-case section says all 33 Martinez collision rows pass the strict
  detector audit;
- the audit section reports `26/33 PASS, 7 FAIL`.

This must be resolved by a real `make test-collision-audit` run before the
paper is promoted.  Until then, the safe manuscript position is:

- Martinez table cross-check status is unverified for promotion;
- collision audit is a blocking diagnostic, not a passed artifact gate;
- no claim of complete phase-exact Cook collision validation should be made.

## Promotion Consequence

Do not promote this seed until one of the following is true:

1. a Unix-like build environment reruns the full `make` suite and updates the
   counts and collision audit status; or
2. the paper is explicitly scoped as a finite-witness artifact with collision
   audit failures disclosed as diagnostics, and the target venue accepts that
   limitation.

The current best next action is to install/use an environment with `make`, run
the dynamic commands from `recheck_plan.md`, and update this note with the exact
command outputs and exit codes.
