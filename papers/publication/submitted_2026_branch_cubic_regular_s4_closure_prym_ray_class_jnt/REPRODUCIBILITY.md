# Reproducibility Note

This note lists the companion scripts and generated files used in
`2026_branch_cubic_regular_s4_closure_prym_ray_class_arithmetic`.

## Scope

The computational material is used to verify explicit arithmetic claims in
Sections 5 and 6 of the manuscript. Database information from the LMFDB is used
only as a consistency check; it is not an input to any proof.

## Environment

- SageMath and Python 3 were used for the computations recorded in the paper.
- Some scripts are pure Python; some audits import `sympy`.
- Run scripts from the paper directory so that relative paths resolve correctly.

## Core scripts

- `artifacts/point_count.py`
  Reproduces point counts of
  `X_A: w^2 = -y(y-1)(256y^3 + 411y^2 + 165y + 32)`
  over `F_p` and `F_{p^2}`. This supports the Frobenius polynomials quoted for
  `Jac(X_A)`.

- `artifacts/conductor_exact.py`
  Records the exact local calculations used in the conductor discussion at
  `p = 3`, including p-adic valuation data for the branch roots.

- `scripts/exp_branch_cubic_rayclass_modform_audit.py`
  Reproduces the class-group and ray-class calculations for
  `K = Q(sqrt(-111))` and the Hecke trace checks attached to the weight-1
  Artin representation.

- `scripts/exp_genus2_jacobian_audit.py`
  Audits the genus-2 Jacobian by computing point counts, `L_p(T)` data at good
  primes, and consistency checks for the explicit formulas in Section 6.

- `scripts/generate_Q_traces_table.py`
  Generates the LaTeX table of Frobenius traces for the Prym threefold `Q`
  included through `sections/generated/prym_traces_table.tex`.

## Generated files used by the manuscript

- `sections/generated/prym_traces_table.tex`
  Included directly in the manuscript as the trace table for the Prym threefold
  `Q`.

## Additional audit scripts

The `scripts/` directory also contains broader audit scripts, including:

- `exp_branch_cubic_arithmetic_audit.py`
- `exp_conductor_xa.py`
- `exp_genus2_simplicity_proof.py`
- `exp_prym_q_analysis.py`

These are supplementary consistency checks for the explicit example.

## Submission packaging

For submission, the manuscript, this note, and the scripts listed above should
be kept together so that a referee can inspect the calculations underlying the
explicit tables and local arithmetic checks.
