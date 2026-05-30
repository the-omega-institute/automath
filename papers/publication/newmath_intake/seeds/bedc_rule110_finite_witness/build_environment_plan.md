# Build Environment Plan: BEDC Rule 110 Finite Witness Artifacts

This is an intake-level environment plan.  It does not promote the seed and does
not create any active paper files.

- note date: 2026-05-31
- source repo: `D:/omega/newmath`
- pinned source ref: `origin/dev`
- pinned source commit: `3fb3d6a0641767388a401883062aa522ea0b397b`
- source subdir: `D:/omega/newmath/rule110`

## Current Blocker

The artifact seed cannot be promoted on the current evidence because the dynamic
suite has not been rerun.  The local probes found:

| Environment | Status |
|---|---|
| Windows PATH | `make`, `mingw32-make`, `gcc`, `cc`, and `clang` not found |
| WSL Ubuntu | can access `/mnt/d/omega/newmath/rule110`, but `make`, `gcc`, and `clang` not found |

Static recheck also found count drift and an unresolved `STATUS.md`
contradiction about Martinez collision rows:

- top-level `tests/test_*.c`: 56 now, previous record 50;
- top-level C LOC: 23914 now, previous record 20167;
- collision audit text simultaneously suggests full strict pass and
  `26/33 PASS, 7 FAIL`.

## Preferred Route

Use WSL Ubuntu as the artifact environment, because it can address the source
tree through `/mnt/d/omega/newmath/rule110` and should match the Unix-oriented
`make` workflow more closely than Windows.

Required tools:

```text
make
gcc or clang
coreutils/findutils
```

Do not install tools or modify the newmath source tree without human approval.

## Verification Commands

After the toolchain exists, run from the source workspace:

```bash
cd /mnt/d/omega/newmath/rule110
make clean
make
make test
make test-collision-audit
make test-scale
```

Record each command's exit code and the key output lines in
`recheck_results.md`.  If a command fails, preserve the failure as artifact
evidence rather than rewriting the claim around it.

## Count Refresh

After `make test`, refresh:

| Evidence | Required result |
|---|---|
| `tests/test_*.c` count | exact count with command |
| C LOC | exact count with command |
| FKernel Lean LOC | exact count with command |
| source `.enum.ct` and `.algo.ct` manifests | exact counts |
| generated `.r110.ct` and `.algo.r110.ct` manifests | exact counts after materialization |
| total `.ct` manifests | exact count after materialization |
| Martinez phase verifier | pass/fail count and log path |
| collision audit | exact `PASS/FAIL` row count and log path |
| scale frontier | exact largest completed scale case |

## Promotion Decision

Promotion is safe only if one of these paths is selected:

1. full artifact route: dynamic suite passes or failures are understood and
   repaired in the source before promotion;
2. diagnostic artifact route: failures remain, but the target venue and paper
   claim explicitly treat them as disclosed limitations rather than passed
   certificates.

Until then, keep this seed in intake and do not create `main.tex`,
`PIPELINE.md`, or any `2026_*` active paper directory for it.
