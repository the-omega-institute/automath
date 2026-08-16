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

The scripts require Python 3.10 or later and `mpmath`.

## Article build

From the article directory, run:

    latexmk -C main.tex
    latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex

Check `main.log` for unresolved references, unresolved citations, and
multiply-defined labels.
