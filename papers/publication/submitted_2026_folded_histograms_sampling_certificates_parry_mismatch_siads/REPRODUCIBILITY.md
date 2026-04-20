Numerical table provenance for `main.tex`

This directory contains the exact generated TeX tables used by the manuscript:

- `generated/tab_canonical_injective_floor_exact_en.tex`
- `generated/tab_rotation_folded_kl_certificate_en.tex`
- `generated/tab_rotation_multiscale_residual_summary_en.tex`
- `generated/tab_rotation_parry_gap_summary_en.tex`
- `generated/tab_iid_sources_fold_vs_parry_ci_en.tex`

These files are emitted from the experiment scripts in the companion source tree:

- `D:\omega\the-omega\docs\papers\auric-golden-phi\2026_golden_ratio_driven_scan_projection_generation_recursive_emergence\scripts\exp_generated_tex.py`
- `D:\omega\the-omega\docs\papers\auric-golden-phi\2026_golden_ratio_driven_scan_projection_generation_recursive_emergence\scripts\exp_rotation_multiscale_residual_summary.py`
- `D:\omega\the-omega\docs\papers\auric-golden-phi\2026_golden_ratio_driven_scan_projection_generation_recursive_emergence\scripts\run_all.py`

Audit-grid conventions used in the paper:

- Rotation sweep: `m in {6,8,10,12,14,16,18}`, `N in {10^4, 3x10^4, 10^5, 3x10^5}`, `beta in {0.2,0.3,0.5,0.6180339887}`, `x0 in {0.123,0.271,0.731}`.
- Rotation families: golden slope, metallic means `alpha_A=[0;A,A,...]` for `A in {2,3,5}`, and resonant stress-test families `[0;B,1,1,...]` for `B in {10,30,100}`.
- IID baselines: `m in {6,8,10,12,14,16,18}`, `N in {2000,5000,10^4,3x10^4,10^5}`, seeds `{1,2,3,4,5}`, confidence level `95%`.

Important scope note:

- The `[0;B,1,1,...]` family is a bounded-type stress test with a large first partial quotient. It is not presented as a genuinely unbounded-type experiment.

Canonical exact table note:

- `generated/tab_canonical_injective_floor_exact_en.tex` is not an averaged scan table. It records exact canonical-slice quantities at `beta = alpha`, computed from the exact Lebesgue factor law together with the exact folded pushforward and Parry block law.
- This table should be backed in the supplementary bundle by a small deterministic script that evaluates the exact factor law and the quantities `L_1(m)`, `KL(pi_m^{fold} || pi_m)`, and `TV(pi_m^{fold}, pi_m)` for the listed values of `m`.
