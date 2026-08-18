# Reproduction

The article's claims are proved analytically in the manuscript. The numerical
calculation below is a consistency check and is not used as a premise of a
theorem.

## Critical-constant check

From the article directory, run:

    python artifacts/verify_critical_constants.py
    python -m unittest discover -s artifacts -p "test_*.py" -v

The script solves
`zeta(sigma_0 - 1) / zeta(sigma_0) = 2`, evaluates the closed forms for
`K_C` and the stable normalization, and computes

    rho_Q = 1 + sum_{q=2}^Q phi(q) q^(-sigma_0)

at `Q = 10^3, 10^4, 10^5, 10^6`. The resulting values of `2 rho_Q^2`
approach the proved context constant `b_C = 8` from below. The default sieve
uses `Q = 10^6`; pass `--max-cutoff Q` to use another final cutoff.

This check requires Python 3.10 or later and `mpmath`.

## Critical Gibbs-geometry simulation

From the article directory, run:

    python artifacts/verify_critical_gibbs_geometry.py

The deterministic run uses seed `20260817`, estimates `mu_C` from 3,000,000
independent critical letters, and draws 30,000 finite-layer Gibbs samples at
each of `m = 200, 800, 2400`.  It writes the complete observed-versus-predicted
tables to `artifacts/critical_gibbs_geometry_check.txt`.  The calculation uses
only the standard library and NumPy.

The script also evaluates two same-data negative controls.  To run the sign
mutation by itself and confirm a nonzero exit status, use:

    python artifacts/verify_critical_gibbs_geometry.py --prediction flip-sign --output -

This substitutes
`+mu_C^(-1-1/alpha) t^(1/alpha) S_alpha` for the theorem's negative law.
The other built-in mutation is:

    python artifacts/verify_critical_gibbs_geometry.py --prediction mu-power --output -

It substitutes `mu_C^(-1/alpha)` for `mu_C^(-1-1/alpha)`.  Both mutations are
expected to print `OVERALL = RED` and exit with status 1.  These simulations
are finite-size consistency checks for signs and constants; they do not test
or prove convergence in distribution.

## Finite-size crossover from direct partition counts

From the article directory, run:

    python artifacts/verify_finite_size_crossover.py

The script computes every `R(N)` through the largest requested Fibonacci
layer by the exact distinct-part subset-sum recurrence. It prints the full
integer histogram `R-value:number of N` for each layer before forming any
weighted sum. The default ladder is `m = 12, 16, 20, 24, 28, 32`, and the
window parameters are `theta = -4, 0, 4`.

The comparison uses

    s_m = sigma_0 + theta / (kappa m)

and checks `Z_m^R(-s_m)/m` against the crossover limit. The negative control
replaces the correct prefactor `2` by `1/2`, making its target four times too
small. The full deterministic output is written to
`artifacts/finite_size_crossover_check.txt`. This is a finite-size
consistency check and is not used in the proof.

## Sharp context-rate reductions

From the article directory, run:

    python artifacts/verify_context_rate.py

This exact-arithmetic check enumerates the two context words through digit
sum 6 and central digits 1 through 9, and compares the central-continuant
factorization on both sides as rational numbers.  It also enumerates every
canonical noncondensed word through digit sum 18, performs the balanced cut
used in the proof, and checks both digit-sum bounds and the continuant product
inequality.  The check has no numerical tolerance.

## Article build

From the article directory, run:

    latexmk -C main
    latexmk -pdfxe main

Check `main.log` for unresolved references, unresolved citations, and
multiply-defined labels.
