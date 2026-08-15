# Stable-Kernel Entropy at Large Scale

This directory contains the article and a separately compiled supplementary
archive.

## Active Article

Compile **main.tex**. Its central theorem spine is:

1. the critical stable-translation quotient estimate;
2. the optimal uniform sufficient moment exponent
   \[
   p_{\alpha,d}=\max\left\{2,\frac{4(d+\alpha)}{d+\alpha+4}\right\};
   \]
3. the finite-covariance law-by-law decomposition into the quadratic
   covariance energy and the nonlinear raw-tail energy.
4. relative-entropy dissipation and an integral representation for two
   symmetric stable heat flows from measure data.

The fractional-heat theorem and its pilot calculation are in
**sec_fractional_heat_relative_entropy.tex**.  The Cayley coefficient
calculus remains a separate arc, while the RKHS/lattice results are
secondary harmonic-analysis and sampling applications.

The literature audit is **artifacts/literature_check.md**. The structural and
theorem-interface verifier is **artifacts/test_verify_stable_spine.py**.

## Archival Supplement

Compile **supplement.tex**. It contains the displaced Cayley--Chebyshev
coefficient hierarchy, higher-order Poisson defects, covariance-proxy
analysis, Doob/Bregman material, and Poisson-strip RKHS and lattice sampling.
Those results are preserved but are not inputs to the focused article.

The **submission_source/** directory is a legacy snapshot of the former
omnibus article and is not a compile root. Submission packaging should be
regenerated from the four active article sources listed above.

## Verification

Run individual checks, not a root-level test discovery:

    python -m unittest artifacts.test_verify_stable_spine -v
    python -m unittest artifacts.test_verify_oracle_A2 -v
    python artifacts/verify_oracle_A2.py
    latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex
    latexmk -pdfxe -interaction=nonstopmode -halt-on-error supplement.tex
