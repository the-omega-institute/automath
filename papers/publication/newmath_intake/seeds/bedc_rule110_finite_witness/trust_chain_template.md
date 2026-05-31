# Trust-Chain Template: BEDC Rule 110 Finite Witness

This is an intake template for future artifact evidence. It is not a completed
trust-chain table and does not promote the seed.

- seed:
  `papers/publication/newmath_intake/seeds/bedc_rule110_finite_witness`
- source repo: `D:/omega/newmath`
- source subdir: `D:/omega/newmath/rule110`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- template date: 2026-05-31

## Preflight Fields

| Field | Value after rerun |
|---|---|
| source commit used |  |
| source branch/ref |  |
| execution environment |  |
| `make --version` |  |
| C compiler and version |  |
| shell/coreutils environment |  |
| log directory |  |

## Command Evidence

| Command | Exit code | Log path | Key result | Promotion consequence |
|---|---:|---|---|---|
| `make clean` |  |  |  |  |
| `make` |  |  |  |  |
| `make test` |  |  |  |  |
| `make test-collision-audit` |  |  |  |  |
| `make test-scale` |  |  |  |  |

## Pinned Expected Evidence Before Rerun

The following entries come from the pinned source status and trust-chain
documents.  They are not a substitute for command logs; they define what the
rerun should confirm or correct.

| Evidence surface | Pinned expected value | Rerun action |
|---|---|---|
| Tier A | cyclic-tag witness shipped | confirm through `make test` and manifest checks |
| Tier B | Rule 110 direct-carrier and Cook packet coverage shipped | confirm generated `.r110.ct` and `.algo.r110.ct` materialization |
| source manifests | 37 `.enum.ct` and 22 `.algo.ct` | count before materialization |
| generated manifests | 59 `.r110.ct` and 22 `.algo.r110.ct` | count after materialization |
| total manifests | 118 `.ct` after materialization | count after `make test` |
| semantic test cases | 32 Mark cases and 470 FKernel/GroundCompiler cases | identify corresponding test logs |
| Martinez phase verifier | 177 phase verifier entries | confirm whether current verifier passes |
| collision rows | 33 rows with conflicting pass/fail surfaces | resolve through `make test-collision-audit` |
| scale frontier | cases through `scale_2p_16t_16384` | confirm through `make test-scale` |
| Cook caveat | experimental behavioral scaffold, not phase-exact construction | preserve in manuscript limitation language |

## Count Evidence

| Evidence | Command | Value before materialization | Value after materialization | Status |
|---|---|---:|---:|---|
| top-level `tests/test_*.c` files | `find tests -maxdepth 1 -name 'test_*.c' | sort | wc -l` |  |  |  |
| C LOC | `wc -l evaluator/*.c encoder/*.c tests/*.c` |  |  |  |
| FKernel Lean LOC | `wc -l ../lean4/BEDC/FKernel/*.lean` |  |  |  |
| source `.enum.ct` manifests | `find manifests -name '*.enum.ct' | sort | wc -l` |  |  |  |
| source `.algo.ct` manifests | `find manifests -name '*.algo.ct' | sort | wc -l` |  |  |  |
| generated `.r110.ct` manifests | `find manifests -name '*.r110.ct' | sort | wc -l` |  |  |  |
| generated `.algo.r110.ct` manifests | `find manifests -name '*.algo.r110.ct' | sort | wc -l` |  |  |  |
| total `.ct` manifests | `find manifests -name '*.ct' | sort | wc -l` |  |  |  |

## Limitation Evidence

| Surface | Result after rerun | Decision |
|---|---|---|
| Martinez phase verifier |  | pass / diagnostic / blocker |
| collision audit rows |  | pass / diagnostic / blocker |
| largest scale case |  | adequate / diagnostic / blocker |
| generated manifest materialization |  | complete / partial / blocker |

## Promotion Decision

After the table is filled, choose exactly one:

- full artifact route: dynamic commands pass and limitations are resolved;
- diagnostic artifact route: limitations remain but are explicitly in scope;
- park: build, materialization, or collision-audit evidence is too weak.
