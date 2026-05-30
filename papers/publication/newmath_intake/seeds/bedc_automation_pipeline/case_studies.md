# Case Studies: BEDC Automation Pipeline

This intake artifact records concrete cases that can support a promoted
workflow paper.  It is a planning table, not manuscript prose.  Each row points
to evidence already present in `D:/omega/automath` or the pinned
`D:/omega/newmath` source snapshot.

## Candidate Case-Study Rows

| Case | Evidence source | Gate or detector | Failure class | Corrective action | Status for promoted paper |
|---|---|---|---|---|---|
| Upper-fibers overlap block | `PROGRAM_BOARD_MACHINE.md` rows for `submitted_2026_upper_fibers_witness_covers_fibonacci_apparition_rj`, `submitted_2026_fibonacci_moduli_cross_resolution_arithmetic_rint`, and `2026_upper_fibers_witness_covers_fibonacci_apparition_fq`; `inner.log` lines preserving hard Stage A block | Deterministic overlap/submitted gate | Later FQ route overlaps earlier submitted/current routes and must not advance randomly | Preserve hard Stage A block until the board explicitly closes, supersedes, merges, or withdraws the prior route | Good case for submitted/overlap governance |
| Fake-extension block after Codex theoremization | `PROGRAM_BOARD_MACHINE.md` rows for `2026_single_primitive_universality_hierarchy`, `2026_joukowsky_elliptic_godel_lorentz_mahler_capacity`, and `2026_elliptic_normalization_branch_geometry_quartic_spectral`; commits such as `358b440bc` and machine-board fake-extension notes | Stage A anti-hollow / delta threshold gate | Agent edits can compile or rephrase without adding substantive theorem content | Mark A-BLOCKED or require manual theorem-deepening instead of continuing the same loop | Good case for anti-hollow theorem-growth control |
| C-INFRA-STUCK classification | `PROGRAM_BOARD_MACHINE.md` rows for `2026_folded_histograms_sampling_certificates_parry_mismatch_etds` and `2026_cayley_chebyshev_poisson_entropy_strip_rkhs_jfa`; `inner.log` preserving structured Stage C terminal error | Stage C terminal-state classifier | Stage C exhausted with Oracle extraction/infra symptoms, not necessarily mathematical failure | Classify as C-INFRA-STUCK and require extraction repair or recovered final-review task before human review | Good case for not misclassifying infrastructure failures as paper failures |
| C-NEAR-PASS classification | `PROGRAM_BOARD_MACHINE.md` row for `2026_coefficient_sup_radial_homotopy_monomial_forms_jdde` | Stage C terminal-state classifier | A manuscript can exhaust nominal Stage C rounds while recent Oracle/Codex verdicts are near acceptance | Mark C-NEAR-PASS and route to final review / possible C+1 override, not ordinary failed | Good case for structured terminal categories |
| Newmath intake isolation | `PROGRAM_BOARD.md` and `newmath_intake/BOARD.md` rows for the three P0 BEDC seeds; direct file check showing no `main.tex`, no `PIPELINE.md`, and no `2026_*` directory under `newmath_intake` | Active-paper detector boundary in `pipeline_auto.py` and human board policy | Seed material could be accidentally interpreted as active publication pipeline input | Keep seeds intake-only until human promotion; store source maps, inventories, risk registers, and checklists without active triggers | Good case for workflow boundary design |
| Rule110 finite-witness limitation | `newmath_intake/seeds/bedc_rule110_finite_witness/artifact_inventory.md`, `limitation_ledger.md`, and pinned `D:/omega/newmath` `rule110/STATUS.md` | Artifact limitation ledger and recheck plan | Strong artifact counts coexist with a collision-audit diagnostic: `26/33 PASS, 7 FAIL` | Require disclosure or fix before promotion; forbid universal Rule 110 proofhood claims | Good case for artifact honesty and non-claim enforcement |

## Selection for First Promoted Draft

For a short CICM presentation-only or workshop paper, use four cases:

1. Newmath intake isolation.
2. Upper-fibers overlap block.
3. Fake-extension block after theoremization.
4. Rule110 finite-witness limitation.

Use C-INFRA-STUCK and C-NEAR-PASS only if the draft has room for a publication
pipeline terminal-state section.  They are valuable but may make a short
presentation paper too broad.

## Evidence to Recheck Before Manuscript Use

- Re-run `rg` on `PROGRAM_BOARD_MACHINE.md` for the named rows and copy the
  exact status text into a manuscript working note.
- Re-read the relevant `inner.log` tail or archived health record for the
  overlap and C-INFRA-STUCK examples.
- Re-run the `newmath_intake` active-trigger check:

```powershell
Get-ChildItem -Recurse -File papers\publication\newmath_intake |
  Where-Object { $_.Name -in @('main.tex','PIPELINE.md') -or $_.FullName -match '\\2026_' }
```

- Re-run or explicitly defer the Rule110 commands in
  `../bedc_rule110_finite_witness/recheck_plan.md`.
