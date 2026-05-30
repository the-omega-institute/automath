# Artifact Rerun Packet: BEDC Rule 110 Finite Witness Artifacts

This is an intake-level rerun packet.  It does not promote the seed and does
not create any active paper files.  It is the execution and recording template
for the first real artifact rerun once a `make` plus C compiler environment is
available.

- packet date: 2026-05-31
- source repo: `D:/omega/newmath`
- source subdir: `D:/omega/newmath/rule110`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- preferred execution environment: WSL Ubuntu or another Unix-like shell with
  `make`, `gcc` or `clang`, `find`, `wc`, and standard coreutils

## Purpose

The seed is blocked because only static counts have been rechecked.  The
dynamic Rule 110 artifact suite has not been rerun, generated `.r110.ct`
manifests are not materialized, and `STATUS.md` contains an unresolved
collision-audit contradiction.  This packet defines the exact evidence required
before any promotion discussion.

## Preflight

Run from WSL or another Unix-like shell:

```bash
cd /mnt/d/omega/newmath/rule110
git -C /mnt/d/omega/newmath rev-parse HEAD
git -C /mnt/d/omega/newmath rev-parse origin/dev
command -v make
command -v gcc || command -v clang
make --version | head -5
```

Record the output in `recheck_results.md`.  If the source commit differs from
the pinned intake commit, add a source update note before using the new run as
promotion evidence.

## Required Dynamic Commands

Run the commands below in order.  Preserve logs and exit codes.

```bash
cd /mnt/d/omega/newmath/rule110
make clean       2>&1 | tee logs/intake_make_clean.log
make             2>&1 | tee logs/intake_make.log
make test        2>&1 | tee logs/intake_make_test.log
make test-collision-audit 2>&1 | tee logs/intake_collision_audit.log
make test-scale  2>&1 | tee logs/intake_test_scale.log
```

If the source tree does not already have a suitable `logs/` directory, create
one in the source workspace before running the commands.  Do not copy large raw
logs into automath intake; record summaries and paths.

## Count Commands

After `make test`, rerun these counts from `/mnt/d/omega/newmath/rule110`:

```bash
find tests -maxdepth 1 -name 'test_*.c' | sort | wc -l
wc -l evaluator/*.c encoder/*.c tests/*.c
wc -l ../lean4/BEDC/FKernel/*.lean
find manifests -name '*.enum.ct' | sort | wc -l
find manifests -name '*.algo.ct' | sort | wc -l
find manifests -name '*.r110.ct' | sort | wc -l
find manifests -name '*.algo.r110.ct' | sort | wc -l
find manifests -name '*.ct' | sort | wc -l
```

Record exact commands, outputs, and whether generated manifests are present
after materialization.

## Result Template

Fill this table in `recheck_results.md` after the rerun:

| Evidence | Command/log | Exit/status | Result | Promotion consequence |
|---|---|---:|---|---|
| `make clean` | `logs/intake_make_clean.log` |  |  |  |
| `make` | `logs/intake_make.log` |  |  |  |
| `make test` | `logs/intake_make_test.log` |  |  |  |
| `make test-collision-audit` | `logs/intake_collision_audit.log` |  |  |  |
| `make test-scale` | `logs/intake_test_scale.log` |  |  |  |
| test C files | count command |  |  |  |
| top-level C LOC | `wc -l evaluator/*.c encoder/*.c tests/*.c` |  |  |  |
| FKernel Lean LOC | `wc -l ../lean4/BEDC/FKernel/*.lean` |  |  |  |
| source `.enum.ct` manifests | count command |  |  |  |
| source `.algo.ct` manifests | count command |  |  |  |
| generated `.r110.ct` manifests | count command |  |  |  |
| generated `.algo.r110.ct` manifests | count command |  |  |  |
| total `.ct` manifests | count command |  |  |  |
| Martinez phase verifier | relevant log line |  |  |  |
| collision audit rows | `logs/intake_collision_audit.log` |  |  |  |
| largest scale case | `logs/intake_test_scale.log` |  |  |  |

## Promotion Decision Rules

Use these deterministic rules after the rerun:

| Outcome | Decision |
|---|---|
| All dynamic commands pass and collision audit is internally consistent | Seed may proceed to human promotion discussion as an artifact/workshop paper. |
| Build and core tests pass, but collision audit remains `26/33 PASS, 7 FAIL` or similar | Seed may only proceed as a diagnostic finite-witness paper if the abstract and limitation ledger disclose the failure. |
| Build fails or generated manifests do not materialize | Do not promote; repair source/toolchain first or park as an artifact-infrastructure note. |
| Counts drift from prior notes but commands pass | Update artifact inventory and trust-chain table before promotion. |
| Source commit changed | Add source update note before any venue decision. |

## Minimum Trust-Chain Table for a Promoted Paper

Before promotion, prepare a compact table with:

- source commit;
- toolchain versions;
- command exit codes;
- manifest counts before and after materialization;
- collision-audit result;
- scale frontier;
- explicit limitation status.

This table should become the core evidence for any CICM artifact, JFR, or JAR
route.  Without it, the seed remains intake-only.
