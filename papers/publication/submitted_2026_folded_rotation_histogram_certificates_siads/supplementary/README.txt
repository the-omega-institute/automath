Supplementary Materials
=======================
"Folded Histograms of Irrational Rotations: Sampling Certificates
 and Structural Mismatch to the Parry Measure"

Haobo Ma and Wenlin Zhang


Contents
--------

scripts/
  Experiment scripts that reproduce all numerical tables and the
  circle-map example in the manuscript.

  Core experiments:
    exp_rotation_fold_vs_parry.py
        Rotation scan: sliding-window microstates -> Fold_m histogram
        vs Parry baseline.  Produces the raw CSV behind Tables 3--5.

    exp_rotation_microstate_kl_certificate.py
        Microstate-level KL certificates with star-discrepancy bounds.
        Produces Table 3 (finite-sample validation).

    exp_rotation_multiscale_residual_summary.py
        Cross-resolution projective TV residuals.
        Produces Table 4.

    exp_iid_sources_fold_vs_parry.py
        IID baselines (Bernoulli and Parry-distributed) with
        confidence envelopes.  Produces Table 6.

    exp_generated_tex.py
        Reads the exported CSV files and emits the LaTeX table
        fragments in generated/.

    exp_circle_map_audit.py
        Self-contained script for the nonlinear circle-map example
        (Section 6.7).  Tunes the standard circle map with K=0.3
        to rotation number phi^{-1}, then reproduces the TV/KL
        values reported in the text.

  Shared utilities:
    common_phi_fold.py       Golden-mean folding and Parry/PF baselines
    common_ostrowski_fold.py Ostrowski numeration (general CF slopes)
    common_fold_map_cache.py Cached fold-map construction
    common_paths.py          Path conventions for the pipeline
    common_tail_budget.py    Tail-budget certificate utilities

generated/
  Pre-built LaTeX table fragments included by the manuscript via
  \input{}.  These files are the direct output of the experiment
  scripts and should not be edited by hand.

    tab_canonical_injective_floor_exact_en.tex  (Table 2)
    tab_rotation_folded_kl_certificate_en.tex   (Table 3)
    tab_rotation_multiscale_residual_summary_en.tex (Table 4)
    tab_rotation_parry_gap_summary_en.tex       (Table 5)
    tab_iid_sources_fold_vs_parry_ci_en.tex     (Table 6)

REPRODUCIBILITY.md
  Audit-grid conventions and provenance notes for all generated tables.


How to run
----------

Requirements: Python >= 3.9, NumPy >= 1.21, Matplotlib >= 3.4.

All scripts are designed to be run from the scripts/ directory:

    cd scripts
    python3 exp_rotation_fold_vs_parry.py
    python3 exp_iid_sources_fold_vs_parry.py
    python3 exp_rotation_microstate_kl_certificate.py
    python3 exp_rotation_multiscale_residual_summary.py
    python3 exp_generated_tex.py
    python3 exp_circle_map_audit.py

The first four scripts write intermediate CSV files to
../artifacts/export/.  The fifth script (exp_generated_tex.py)
reads those CSV files and writes the LaTeX fragments in generated/.

The circle-map script is self-contained and writes its output to
scripts/circle_map_audit_results.txt.

Expected wall-clock time on a single core: approximately 10--20
minutes for the full pipeline (dominated by the rotation scan at
large N).  Each script prints progress to stdout.
