# Recheck Plan: BEDC Rule 110 Finite Witness Artifacts

This plan lists the evidence that must be rechecked before promotion.  It is
not a command log.

## Source Snapshot

- Source repo: `D:/omega/newmath`
- Intake source ref: `origin/dev`
- Intake source commit: `3fb3d6a0641767388a401883062aa522ea0b397b`

If the promoted paper uses a newer commit, record a source update note with the
old commit, new commit, changed artifact paths, and changed counts.

## Commands

Run from the source workspace, not from automath intake:

```powershell
cd D:\omega\newmath\rule110
make clean
make
make test
make test-collision-audit
make test-scale
```

## Counts to Recompute

| Count | Command family |
|---|---|
| test binaries | `ls tests/test_*.c | wc -l` or PowerShell equivalent |
| C LOC | `wc -l evaluator/*.c encoder/*.c tests/*.c` or equivalent |
| FKernel Lean LOC | `wc -l ../lean4/BEDC/FKernel/*.lean` or equivalent |
| `.enum.ct` manifests | `find manifests -name '*.enum.ct'` |
| `.algo.ct` manifests | `find manifests -name '*.algo.ct'` |
| `.r110.ct` manifests | `find manifests -name '*.r110.ct'` |
| `.algo.r110.ct` manifests | `find manifests -name '*.algo.r110.ct'` |
| total `.ct` files after materialization | `find manifests -name '*.ct'` after `make test` |

## Promotion Decision Points

- Is `make test` still exit 0?
- Is the scale frontier still `scale_2p_16t_16384`?
- Does the Martinez phase verifier still report 177 PASS entries?
- Is the collision audit still 26/33 PASS and 7 FAIL, or has it changed?
- Are all 37 enum-derived and 22 algorithm-derived manifest counts still
  valid?
