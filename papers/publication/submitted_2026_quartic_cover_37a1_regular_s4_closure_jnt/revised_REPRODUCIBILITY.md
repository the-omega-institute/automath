# Reproducibility note

This note records the finite computations used in the manuscript and the
corresponding source files included with the revised submission. The scripts are
intended as independent audits of explicit calculations appearing in the text;
the mathematical arguments in the manuscript state which inputs are formal,
which are symbolic computations, and which are numerical consistency checks.

## Scripts and outputs

| Script/file | Role | Manuscript location | Output |
| --- | --- | --- | --- |
| `revised_exp_branch_cubic_arithmetic_audit.py` | Audits the cubic generators, discriminants, maximal-order basis, order indices, and prime decompositions at 3 and 37. | Proposition 2.3 | `artifacts/export/branch_cubic_arithmetic_audit.json` when run |
| `revised_exp_branch_cubic_rayclass_modform_audit.py` | Audits the ideal powers in `Q(sqrt(-111))`, the norm-form check for the class group generator, and root-count traces for the branch cubic and maximal-order cubic. | Theorem 5.4 and Theorem 5.7 | `artifacts/export/branch_cubic_rayclass_modform_audit.json` when run |
| `revised_exp_genus2_jacobian_audit.py` | Counts points on `X_A` over `F_p` and `F_{p^2}`, computes Frobenius polynomial coefficients, and records reducibility checks at good primes. | Proposition 6.1 | `artifacts/export/genus2_jacobian_audit.json` when run |
| `revised_generate_Q_traces_table.py` | Computes the first trace values for the Prym threefold factor by point counting on the regular `S_4`-closure fibers and subtracting the known factors. | Proposition 6.10 | `sections/generated/prym_traces_table.tex` |
| `revised_exp_prym_q_analysis.py` | Provides auxiliary point-count and trace consistency checks for the elliptic factors, `X_A`, and the Prym threefold profile. | Section 6.4 | `artifacts/export/prym_q_analysis.json` when run |

## Local conductor calculation at 3

The equality `delta_3 = 1` is proved in the text from the local orbit and
different calculation in Section 6.5. No separate `conductor_exact.py` file is
used in this source tree. The relevant finite data are the `3`-adic reduction
of the branch roots, the single cubic orbit above `y = 1`, and the different
exponent contribution recorded in Theorem 6.16.

## Database use

Data from the LMFDB are used only as consistency checks for elliptic-curve
metadata and are not used as inputs to any proof.
