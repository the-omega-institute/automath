# Current Static Status Map: BEDC Rule 110 Finite Witness

This is an intake-level static map of the local `D:/omega/newmath/rule110`
source tree.  It does not promote the seed, does not run the dynamic artifact
suite, and must not be treated as a promoted artifact appendix.

## Snapshot Warning

- intake pinned commit: `3fb3d6a0641767388a401883062aa522ea0b397b`
- local source HEAD observed during this pass:
  `dc06a0ecb02e586142dda3932749bcfe6fe3c9ba`
- local source branch/status observed: `auto-dev...origin/auto-dev`

The static observations below are useful as a current workspace baseline.  They
do not replace the pinned source evidence and do not remove the need for a
source update note if the local `dc06a0...` snapshot is used for promotion.

## Source Layout Observed

Top-level `rule110` entries observed in the local source tree:

| Path | Role |
|---|---|
| `Makefile` | dynamic build and test entry point |
| `STATUS.md` | reported artifact status and known collision-audit text |
| `README.md`, `ROADMAP.md`, `LICENSE` | source documentation |
| `docs/` | literature and artifact notes |
| `encoder/` | Cook/tag-system encoding implementation |
| `evaluator/` | Rule 110 and cyclic-tag evaluators |
| `history/` | historical or generated support material |
| `lean-side/` | Lean-side bridge material |
| `manifests/` | source and generated `.ct` manifest area |
| `tests/` | C test programs |
| `tools/` | auxiliary tooling |

## Pinned Origin/Dev STATUS Evidence

The pinned source status is evidence-rich and should be carried forward before
any promotion decision.  It reports the following surfaces:

| Surface | Pinned reported evidence | Promotion consequence |
|---|---|---|
| Tier A | cyclic-tag witness shipped | usable as a finite witness claim after rerun or explicit pinned-status citation |
| Tier B | Rule 110 physical witness shipped for FKernel direct-carrier and Cook packet coverage | usable only with finite-scope language |
| direct-carrier coverage | `.r110.ct` covers FKernel/GroundCompiler `.enum.ct` manifests | needs materialization/rerun before artifact submission |
| Cook packet coverage | `.algo.r110.ct` covers 22 `.algo.ct` manifests | must remain outside phase-exact universality claims |
| tests | `make test` reported exit 0 | intake must rerun before using as current command evidence |
| Lean trust boundary | 0 axiom invariant reported | must be rechecked if promoted as a verified artifact paper |
| manifest counts | 37 `.enum.ct`, 22 `.algo.ct`, 59 `.r110.ct`, 22 `.algo.r110.ct`, 118 total `.ct` after materialization | current static checkout does not materialize generated manifests, so rerun is required |
| semantic cases | 32 Mark cases and 470 FKernel/GroundCompiler semantic cases | strong candidate evidence for a finite-witness paper |
| scale surface | 6 Cook packet scale cases through `scale_2p_16t_16384` | needs rerun before claiming artifact adequacy |

The safe reading is: the seed is blocked by missing current rerun evidence, not
by missing source content.

## Static Counts Observed

These counts were read from the local source filesystem without running
`make`, `make test`, or generated-manifest materialization.

| Count family | Current local value | Promotion consequence |
|---|---:|---|
| `tests/test_*.c` files | 56 | Confirms the earlier static drift from the old reported count of 50. |
| source `.enum.ct` manifests | 37 | Matches the prior static recheck. |
| source `.algo.ct` manifests | 22 | Matches the prior static recheck. |
| generated `.r110.ct` manifests | 0 | Generated manifests are not materialized in the static checkout. |

## Makefile Dynamic Gates Observed

The local `Makefile` contains the dynamic targets required by the rerun packet:

| Target | Observed location | Promotion use |
|---|---|---|
| `all` | `Makefile:46` | Build standalone and encoder binaries. |
| `test` | `Makefile:300` and appended target blocks | Run the main test family and materialize generated manifests. |
| `test-collision-audit` | `Makefile:324` | Run strict Cook/Martinez collision audit. |
| `test-scale` | `Makefile:453` | Run scale-frontier packet test. |
| `clean` | `Makefile:330` | Remove generated binaries and artifacts before rerun. |

These targets were located only; they were not executed in this pass.

## STATUS.md Conflict Still Present

The local `STATUS.md` still contains both of the following status surfaces:

| Surface | STATUS.md location | Text-level consequence |
|---|---|---|
| strict collision audit reported as passing | lines 89-90 | Says all 33 collision rows pass strict detector audit. |
| strict table audit reports failures | lines 147-148 | Reports `26/33 PASS, 7 FAIL` while also saying 33 rows matched the paper table. |

Until a real `make test-collision-audit` run resolves or explains this conflict,
the safe paper position remains:

- collision audit is not a passed artifact gate;
- Martinez collision table status is unverified for promotion;
- finite-witness claims must not be inflated into phase-exact universality
  claims.

## Pinned Trust-Chain Evidence

`rule110/docs/trust_chain.md` supplies the intended evidence stack:

| Layer | Pinned content | Safe use |
|---|---|---|
| Rule 110 evaluator | truth table `{0,1,1,1,0,1,1,0}`, fixed-zero boundary, deterministic update | implementation-level evaluator description |
| cyclic-tag evaluator | head `1` appends then drops, head `0` drops, program counter modulo productions, halting by empty/step/OOM | finite execution semantics |
| GroundCompiler encoder | `b0 -> 0`, `b1 -> 10`, terminator `11` | ties artifacts to `ChannelEncoding.lean` |
| Minimal prototype reject surface | reject reasons aligned with `MinimalPrototype.lean` | audit/checklist evidence |
| Cook layer caveat | experimental behavioral scaffold rather than phase-exact Cook 2004 construction | mandatory limitation language |

## Remaining Required Dynamic Evidence

Before any promotion, run the dynamic suite from `artifact_rerun_packet.md` in a
toolchain-equipped environment and record exit codes:

```bash
make clean
make
make test
make test-collision-audit
make test-scale
```

Only after those commands are run can the seed decide whether to promote as:

- a clean artifact/workshop paper;
- a diagnostic finite-witness paper with disclosed collision-audit failures;
- or a parked artifact-infrastructure route.
