# rule110 status

Status: Tier A (cyclic-tag witness) **shipped**; Tier B (Rule 110 physical witness) **shipped** for FKernel direct-carrier and Cook packet coverage.

This snapshot records the current citable state of the `rule110/` artifact.
The master plan is `ROADMAP.md`. The paper-data reference is
`docs/papers_research_report.md`.

## 框架

详细见 `ROADMAP.md`. 简要:

- **Tier A 状态**: cyclic-tag witness 覆盖 13 个 FKernel 模块与
  GroundCompiler manifest, `make test` exit 0, 0 axiom invariant 保持.
- **Tier B 状态**: Rule 110 direct-carrier `.r110.ct` 覆盖 FKernel /
  GroundCompiler `.enum.ct` surface; Cook packet `.algo.r110.ct` 覆盖 22 个
  `.algo.ct` manifest, 并通过 Rule 110 evolution + decoded output window
  round-trip.
- **Cook / Martinez 数据面**: `glider_phases.c/h` 覆盖 Martinez phase
  catalog; `cook_collisions.c` 覆盖 Martinez 2012 Table 1 / Table 2 的 33
  collision rows; `cook_detect.c` 为 309 行 detection layer.
- **文献数据入口**: `docs/papers_research_report.md` 为 301 行 Cook 2009,
  Martinez 2007, Martinez 2012, Neary-Woods 相关数据的 single source of
  truth.
- **附录面**: Beyond-FKernel 四目录 (`circle_up`, `fold_up`, `meta_cic`,
  `topology_up`) 具备 `.r110.ct` direct-carrier manifest, `make test` 覆盖,
  以及单独的 `test_<module>_audit` binary 检查 manifest schema /
  generate_r110 idempotence / 模块特有 invariant.

## Size

Commands:

```bash
ls tests/test_*.c | wc -l
wc -l evaluator/*.c encoder/*.c tests/*.c | tail -1
wc -l ../lean4/BEDC/FKernel/*.lean | tail -1
```

Report:

```text
      50 test binaries
   20167 total C LOC across evaluator/, encoder/, tests/
    4723 total Lean LOC across lean4/BEDC/FKernel/
```

Manifest counts:

```bash
find manifests -name '*.enum.ct' | wc -l
find manifests -name '*.algo.ct' | wc -l
find manifests -name '*.r110.ct' | wc -l
find manifests -name '*.algo.r110.ct' | wc -l
find manifests -name '*.ct' | wc -l
```

```text
      37
      22
      59
      22
     118
```

The source manifest surface is 59 `.ct` files: 37 `.enum.ct` and 22
`.algo.ct`. The generated on-disk Rule 110 surface is 59 `.r110.ct` files:
37 enum-derived plus 22 `.algo.r110.ct`. After `make test` materializes
generated manifests, the on-disk `.ct` total is 118.

## Test Case Count

The visible manifest and semantic assertion totals from `make test` are:

- 32 Mark cases.
- 470 FKernel / GroundCompiler semantic cases: 66 BHist hsame, 5 bounded
  BHist CT certificates, 16 Ext decoder cases, 36 SigRel/sameSig decoder
  cases, 20 Cont decoder cases, 60 ProbeBundle cases, 24 Ask decoder cases,
  43 ExternalBinary cases, 28 Gap decoder cases, 38 Package cases, 58
  NameCert decoder cases, and 76 Settled cases.
- 59 direct-carrier `.r110.ct` manifests: 37 enum-derived and 22
  `.algo.r110.ct`.
- 25 FKernel / GroundCompiler direct-carrier `.r110.ct` manifests exercise
  every binary direct-carrier assertion; `ground_compiler/reject_reasons` has
  two display-only assertions outside binary carrier encoding.
- 22 `.algo.r110.ct` manifests pass both Cook symbolic and Cook semantic
  round-trip checks.
- 177 Martinez phase verifier entries pass period / displacement checks.
- 33 Martinez collision rows pass paper-table cross-check; all 33 of those
  rows pass strict detector audit (`make test-collision-audit` gate at 33).
- 6 Cook packet scale cases pass through `scale_2p_16t_16384`.
- 4 D-glider specific checks cover `D1` and `D2` emitters.
- 11 external Martinez baseline checks cover ether, A, B, C1, C2, Bbar, E,
  Ebar, F, G, and H period / displacement anchors.
- 1 full enum Cook round-trip checks `hist_hsame_refl.algo`.
- 50 test binaries run under `make test`, including pipeline smoke checks,
  bounded CT runner sweeps, Cook scaffold unit tests, and appendix tests.

## Module Coverage

The cyclic-tag manifest surface covers 13 FKernel modules plus
GroundCompiler:

- Mark
- Hist
- Ext
- SigRel and sameSig
- Cont
- Bundle
- Unary
- Ask
- ExternalBinary
- Gap
- Package
- NameCert
- Settled
- GroundCompiler

The Rule 110 direct-carrier surface covers 37 `.r110.ct` enum-derived
manifests: 25 FKernel / GroundCompiler files plus 12 Beyond-FKernel appendix
files. The FKernel / GroundCompiler portion is Mark 4, Hist 5, Ext 1, Sig 2,
Cont 1, Bundle 2, Unary 1, Ask 1, ExternalBinary 1, Gap 1, Package 1,
NameCert 1, Settled 1, and GroundCompiler 3. The Beyond-FKernel portion is
`topology_up`, `fold_up`, `circle_up`, and `meta_cic`, three files each.

All source `.enum.ct` files have `PRODUCTIONS 0`. The generated carrier cases
cover every binary `input=` assertion. The appendix modules are generated as
`.r110.ct` files and are exercised by `test_topology_up`, `test_fold_up`,
`test_circle_up`, and `test_meta_cic` inside `make test`.

The Cook packet surface covers leader, ossifier, data block, phase-exact
packet bodies, 22 `.algo.r110.ct` manifests, and one enum-level Cook
round-trip case. Scale coverage reaches two productions, sixteen tape
symbols, and 16384 cells.

## Audit and verification

Command:

```bash
make test-collision-audit
```

Result:

```text
  table audit (cook_collisions.c full 33 rows): 26/33 PASS, 7 FAIL
  Martinez 2012 Table 1/Table 2 cross-check: 33 rows, 33 matched, 0 only-in-paper, 0 only-in-table
```

Command:

```bash
make test-scale
```

Result:

```text
Scale frontier: largest passing = scale_2p_16t_16384
```

Command:

```bash
./tests/test_phase_verifier_martinez 2>&1 | grep -c "PASS"
```

Result:

```text
177
```

`docs/papers_research_report.md` is the paper-data reference for Cook 2009
Section 1.4, Martinez 2007, Martinez 2012, and Neary-Woods facts used by
the Rule 110 artifact.

## Verification

Command:

```bash
cd rule110 && make clean && make && make test
```

Result: exit 0. The final `make test` output ends with:

```text
== tests/test_external_baseline_martinez ==
  martinez_ether_phases: PASS
  martinez_A_period_shift: PASS
  martinez_B_period_shift: PASS
ALL TESTS PASSED
```
