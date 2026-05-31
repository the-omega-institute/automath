# P0 Source Extraction Pass: BEDC Intake

This file records the first active source-moving pass for the three P0 BEDC
seeds.  It is intake-only evidence.  It does not promote any seed into an
active paper track and must not be used by the daemon as a `2026_*` manuscript
directory.

- extraction date: 2026-05-31
- source repo: `D:/omega/newmath`
- source ref used for evidence: `origin/dev`
- pinned source commit:
  `3fb3d6a0641767388a401883062aa522ea0b397b`
- automath intake root: `papers/publication/newmath_intake`

## Boundary

This pass deliberately moves only structured source evidence into seed-level
intake documents:

- source paths;
- exact Lean declaration names;
- artifact counts reported by pinned status files;
- trust-chain and limitation surfaces;
- promotion blockers and handoff tasks.

It does not create:

- `papers/publication/2026_*`;
- seed-local `main.tex`;
- seed-local `PIPELINE.md`;
- promoted `SOURCE_MAP.md`, `THEOREM_LIST.md`, `ARTIFACT_INVENTORY.md`, or
  `BIB_SCOPE.md`.

## Automation Pipeline Seed

Seed:
`papers/publication/newmath_intake/seeds/bedc_automation_pipeline`

Pinned source evidence moved from:

- `papers/bedc/parts/visions/audit_map_methodology/automated_theory_discovery_pipeline_calculus.tex`
- `lean4/scripts/README.md`
- `lean4/scripts/codex_formalize.py`
- `lean4/scripts/critical_path.py`
- `lean4/scripts/phase_d_lint.py`
- `papers/bedc/scripts/codex_revise.py`
- `papers/bedc/tools/auto-ai-quality/README.md`

The source contains a manuscript-ready discovery-gate spine:

| Source label | Intake role |
|---|---|
| `thm:automated-discovery-dna-completeness-obligation` | motivates why source maps and artifact ledgers are load-bearing |
| `cor:automated-discovery-statement-code-insufficient` | blocks treating statement generation as discovery |
| `thm:automated-discovery-mechanical-not-discovery` | separates mechanical edits from publishable contribution |
| `thm:automated-discovery-compression-not-discovery` | blocks compression-only novelty claims |
| `thm:automated-discovery-certificate-ledger-required` | justifies deterministic ledger checks |
| `thm:automated-discovery-positive-implies-discovery` | gives the positive gate after nontrivial classifier shift |
| `thm:automated-discovery-scored-claims-public-weights` | supports transparent scoring rather than private taste |
| `thm:automated-discovery-gate-kind-sound` | states gate-kind soundness |
| `thm:automated-discovery-demotion-soundness` | supports demoting unsupported claims |
| `thm:automated-discovery-lineage-dag` | supports lineage tracking and non-random routing |
| `thm:automated-discovery-lowest-score-not-best-target` | motivates scheduler discipline |
| `thm:automated-discovery-selection-favours-classifier-change` | explains why deep route changes outrank easy edits |
| `thm:automated-discovery-no-unpaid-discovery` | blocks novelty claims without recorded evidence |
| `thm:automated-discovery-pipeline-safety` | main safety theorem for the pipeline boundary |
| `thm:automated-discovery-pipeline-theorem` | main pipeline theorem candidate for a promoted two-page draft |
| `prin:automated-discovery-principle` | expository principle for the introduction |

Current consequence:

- This seed is the fastest P0 route.
- It can support a CICM presentation-only draft after explicit promotion.
- Before promotion, final live venue checking and source-claim narrowing remain
  required.

## Finite Kernel Calculus Seed

Seed:
`papers/publication/newmath_intake/seeds/bedc_finite_kernel_calculus`

Pinned source evidence moved from:

- `lean4/BEDC/FKernel/Mark.lean`
- `lean4/BEDC/FKernel/Hist.lean`
- `lean4/BEDC/FKernel/Ext.lean`
- `lean4/BEDC/FKernel/Cont.lean`
- `lean4/BEDC/FKernel/Ask.lean`
- `lean4/BEDC/FKernel/Bundle.lean`
- `lean4/BEDC/FKernel/Sig.lean`
- `lean4/BEDC/FKernel/Gap/Core.lean`
- `lean4/BEDC/FKernel/Package/Core.lean`
- `lean4/BEDC/FKernel/NameCert.lean`
- `lean4/BEDC/GroundCompiler/MainTheorems.lean`
- `lean4/BEDC/GroundCompiler/ChannelEncoding.lean`
- `lean4/BEDC/GroundCompiler/MinimalPrototype.lean`

The current exact-name evidence is not empty.  The real blocker is narrower:
the seed has many local constructor, equivalence, determinacy, package,
certificate, and compiler-boundary declarations, but it still needs a selected
manuscript-scale packaging theorem or an explicitly modest short-note route.

Current consequence:

- Do not describe this seed as waiting for content.
- The next Codex-safe work is selection and packaging:
  - choose the finite-kernel manuscript spine;
  - decide whether `Sig`, `Package`, `Gap`, and `NameCert` move into the core
    or an appendix;
  - prepare a source-side work order for a theorem such as
    `finite_kernel_interface_soundness`.
- Journal-style promotion remains blocked until that packaging theorem or
  equivalent theorem family exists and is source-verified.

## Rule110 Finite Witness Seed

Seed:
`papers/publication/newmath_intake/seeds/bedc_rule110_finite_witness`

Pinned source evidence moved from:

- `rule110/STATUS.md`
- `rule110/README.md`
- `rule110/ROADMAP.md`
- `rule110/docs/trust_chain.md`
- `rule110/docs/manifest_format.md`
- `rule110/docs/collision_audit_findings.md`
- `rule110/docs/papers_research_report.md`
- `rule110/evaluator/`
- `rule110/encoder/`
- `rule110/manifests/`
- `rule110/tests/`
- `rule110/Makefile`

Pinned status evidence reports:

| Surface | Reported evidence |
|---|---|
| Tier A | cyclic-tag witness shipped |
| Tier B | Rule 110 physical witness shipped for FKernel direct-carrier and Cook packet coverage |
| Lean coverage | 13 FKernel modules plus GroundCompiler manifest coverage |
| Tests | `make test` reported exit 0 in the status file |
| Lean trust | 0 axiom invariant reported |
| Manifest families | 37 `.enum.ct`, 22 `.algo.ct`, 59 `.r110.ct`, 22 `.algo.r110.ct`, 118 total `.ct` after materialization |
| Test scale | 50 test binaries, 20,167 C LOC, 4,723 Lean LOC across FKernel |
| Semantic cases | 32 Mark cases and 470 FKernel/GroundCompiler semantic cases |
| Cook/Martinez data | 177 phase verifier entries and 33 collision rows described in documentation |

Pinned limitation evidence also reports a conflict:

- one status surface says all 33 collision rows pass strict detector audit;
- another surface reports `26/33 PASS, 7 FAIL` for the table audit.

Current consequence:

- This seed is not content-empty; it is evidence-rich but dynamically
  unverified in the automath intake environment.
- Promotion is blocked by rerun evidence, not by missing narrative.
- The safe route is either a clean artifact/workshop route after the dynamic
  suite passes, or a diagnostic finite-witness paper with the collision-audit
  limitation explicitly in scope.

## Immediate P0 Ordering

| Rank | Seed | Reason | Next non-promotion task |
|---:|---|---|---|
| 1 | `bedc_automation_pipeline` | has the clearest fast presentation route and a compact theorem/gate spine | final source-claim narrowing and live venue check after promotion command |
| 2 | `bedc_rule110_finite_witness` | has strong artifact evidence but needs dynamic rerun | run or schedule the rerun packet and fill the trust-chain template |
| 3 | `bedc_finite_kernel_calculus` | has exact Lean material but needs packaging theorem selection | complete the packaging-theorem work order or choose a narrow short-note route |

## Guard Command

After any further intake edits, run:

```powershell
& 'C:\Users\zwl62\AppData\Local\uv\cache\archive-v0\4-D8f85EmHyOmKxpAE20H\Scripts\python.exe' D:\omega\automath\papers\publication\newmath_intake\check_intake.py
```

Expected result:

```text
OK: newmath intake seeds are not active paper tracks
```
