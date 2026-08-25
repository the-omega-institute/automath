# Reproducibility note

This note records the finite computations used in the manuscript and the
corresponding source files included with the submission. The scripts are
intended as independent audits of explicit calculations appearing in the text;
the mathematical arguments in the manuscript state which inputs are formal,
which are symbolic computations, and which are numerical consistency checks.

## Environment

The outputs below were generated with Python 3.10.11. The two branch-cubic
audit scripts require SymPy 1.13.1; the genus-two audit, Prym profile, and trace
table generator use only the Python standard library. No external database is
required.

## Scripts and outputs

| Script/file | Role | Manuscript location | Output |
| --- | --- | --- | --- |
| `revised_exp_branch_cubic_arithmetic_audit.py` | Audits the cubic generators, discriminants, maximal-order basis, order indices, and prime decompositions at 3 and 37. | Proposition 2.3 | `artifacts/export/branch_cubic_arithmetic_audit.json` when run |
| `revised_exp_branch_cubic_rayclass_modform_audit.py` | Audits the ideal powers in `Q(sqrt(-111))`, the norm-form check for the class group generator, and root-count traces for the branch cubic and maximal-order cubic. | Theorem 5.4 and Theorem 5.7 | `artifacts/export/branch_cubic_rayclass_modform_audit.json` when run |
| `revised_exp_genus2_jacobian_audit.py` | Counts points on `X_A` over `F_p` and `F_{p^2}`, computes Frobenius polynomial coefficients, and records reducibility checks at good primes. | Proposition 6.1 | `artifacts/export/genus2_jacobian_audit.json` when run |
| `revised_generate_Q_traces_table.py` | Counts the regular `S_4`-closure fibre by fibre from decomposition and inertia groups, then extracts the Prym threefold traces. Cross-checks `a_1(Q) = a_1(Y) - a_1(E_res)` for `Y = X/C_4` and reproduces the model point counts of `E`, `E_res`, and `X_A` at every good prime below 120. | Proposition 6.11 | `revised_prym_traces_table.tex` and `sections/generated/revised_prym_traces_table.tex` |
| `revised_exp_prym_q_analysis.py` | Provides auxiliary point-count and trace consistency checks for the elliptic factors, `X_A`, and the Prym threefold profile. | Section 6.4 | `artifacts/export/prym_q_analysis.json` when run |

The quotient controls test the finite-fibre criterion; the contribution above
`y = infinity` is pinned by the local branch expansion in the proof and by its
exact Gaussian-rational assertion in the trace-table generator.

## Commands and expected outputs

| Command | Expected output | SHA-256 |
| --- | --- | --- |
| `python revised_exp_branch_cubic_arithmetic_audit.py` | `artifacts/export/branch_cubic_arithmetic_audit.json` | `5d8e652a2a126b4af9d05b74c1dfee53e1a2a5eb529d6889613b9a110a74ca33` |
| `python revised_exp_branch_cubic_rayclass_modform_audit.py` | `artifacts/export/branch_cubic_rayclass_modform_audit.json` | `44df31999c6146ec1fb1da8592b0f09af4b5a63c53f12b7bf3c9fa572c8d15f6` |
| `python revised_exp_genus2_jacobian_audit.py` | `artifacts/export/genus2_jacobian_audit.json` | `706bc789ae9c993e75ea9d606fd0a1cbce496800ab6dd947dcd2e3f3ccf9cc8c` |
| `python revised_exp_prym_q_analysis.py` | `artifacts/export/prym_q_analysis.json` | `cbd57f98b936a912c2f6826379326de36007d15774e54e8a7b23d7d94d185e8b` |
| `python revised_generate_Q_traces_table.py` | `revised_prym_traces_table.tex`; `sections/generated/revised_prym_traces_table.tex` | `1ab450bd0fb9c3ce321e244437606dcaa23d886d4d0b5a039c5e91e98c611156` |

The optional command `python revised_generate_Q_traces_table.py --diagnose-prime P`
prints the inertia group, decomposition group, residue degree, and rational-point
contribution of every rational branch fibre at the good prime `P`.

## Role in the proofs

The exact cubic-field arithmetic, ideal arithmetic, genus-two Frobenius
polynomials, closure-fibre counts, and local branch expansion reproduce finite
calculations used in the corresponding proofs. The quotient self-matches, the
independent `Y/E_res` trace route, divisibility and Weil-bound checks, and the
auxiliary Prym profile are consistency checks. They are not substituted for the
arguments in the manuscript.

## Local conductor calculation at 3

The equality `delta_3 = 1` is proved in the text from the local orbit and
different calculation in Section 6.5. No separate `conductor_exact.py` file is
used in this source tree. The relevant finite data are the `3`-adic reduction
of the branch roots, the single cubic orbit above `y = 1`, and the different
exponent contribution recorded in Theorem 6.17.

## Database use

No external database is required to run the scripts. Data from the LMFDB are
used only as consistency checks for elliptic-curve metadata and are never inputs
to a proof.
