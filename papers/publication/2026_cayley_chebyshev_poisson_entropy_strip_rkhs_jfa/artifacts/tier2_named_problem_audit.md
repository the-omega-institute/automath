# Tier-2 Named-Problem Audit

Checked 2026-08-14 (Asia/Singapore). The primary printed source is
O. T. Johnson, *A de Bruijn identity for symmetric stable laws*,
arXiv:1310.2045 (2013), Section 7, pp. 16--17. The arXiv source and PDF were
both inspected. Searches covered the arXiv API and full search, Crossref,
the Semantic Scholar and zbMATH records/forward citations already inspected
in the 2026-08-08 and 2026-08-10 passes recorded in `literature_check.md`,
and exact-title/phrase queries for later stable-MMSE, de Bruijn, and
nonsymmetric-stable entropy work. The live Semantic Scholar endpoint returned
HTTP 429 and the live zbMATH endpoint returned HTTP 422 in this pass; those
failures are not represented as successful searches. No later source located
in the completed searches claims to settle any of the three questions below.
This is evidence of current status, not a proof of absence from all literature.
The deceptively close title M. Hirata, A. Nemoto, and H. Yoshida, *An Integral
Representation of the Relative Entropy*, Entropy 14 (2012), 1469--1477,
DOI 10.3390/e14081469, was also checked: its abstract and theorem regime are
Gaussian heat flow, not Johnson's stable interpolation.

## Three Printed Open Problems

1. **Johnson, Open Problem 1 (MMSE-score projection).** Exact quote:
   "It would be of interest to prove a corresponding result for the MMSE score
   $\rho^M$ of Definition 3.1." Here "corresponding" refers to the
   preceding conditional-expectation (projection) identity for the Fisher
   score. **No later source located.**

2. **Johnson, Open Problem 4 (integral representation).** Exact quote:
   "It would be of interest to provide a similar
   representation of $D(f \Vert g_s^{(\alpha)})$ as an integral, using (17)."
   **No later source located. Finite-variance Cauchy case proved** in
   Theorem `thm:johnson-cauchy-integral-representation` of this manuscript;
   the general symmetric-stable question remains open in the searched record.

3. **Johnson, Open Problem 6 (remove symmetry).** Exact quote:
   "Finally, it would be of interest to extend all this work to
   more general (non-symmetric) families of stable laws, removing restrictions on the
   parameterization made in Definition 2.1." **No later source located.**

## Machinery-to-Problem Map

- Problem 1: the paper has translate-mixture quotients and the two-solution
  Bregman derivative (`prop:compact-window-bregman-identity`), but no MMSE
  score convolution formula. The missing object is precisely a conditional
  projection identity for Johnson's $\rho^M$; none of the Laurent, tail-energy,
  or RKHS estimates supplies it.
- Problem 4: `prop:compact-window-bregman-identity` already differentiates
  relative entropy for two simultaneous Cauchy semigroup solutions, while
  `thm:poisson-kl-doob-tail` closes the large-time endpoint. The missing step
  was to conjugate Johnson's interpolation to
  $(P_q*\mu,P_q*P_s)$ and close the $q\downarrow0$ endpoint. The new theorem
  proves exactly that for every finite-variance input, with extended-valued
  relative entropy allowed.
- Problem 6: the stable-kernel theorems use isotropic symmetric densities and
  the Bregman proof uses a symmetric jump kernel. A skew-stable heat kernel,
  its nonsymmetric generator/adjoint pairing, and replacement domain bounds
  are all missing. Symmetry is structural in the current proof, not cosmetic.

## Routes B, C, and D

- **B (standard objects):** the canonical standard-object map is the exact
  dilation conjugacy between Johnson's Cauchy interpolation and the Cauchy
  convolution semigroup. The Cayley chart also maps the Cauchy law to Haar
  measure, but the resulting Laurent modes remain computational machinery,
  not a separate standard-object theorem. The isotropic stable heat kernels
  in the moment-threshold theorem are already standard objects.
- **C (hypotheses):** finite variance is used to obtain a compact quotient
  range and the $q\to\infty$ endpoint in the new proof. It may be stronger
  than necessary, but removing it requires a finite-entropy domain theorem
  beyond the present cutoff argument. Symmetry/isotropy is essential to the
  current Green pairing. Regular variation is essential only for the stated
  missing-top-moment boundary limit, not for the law-by-law stable tail
  decomposition.
- **D (sharpness/converses):** the paper already has a matching counterexample
  below the uniform stable moment exponent and an iff tail-energy criterion.
  The plausible unclosed converse is the higher-order analytic moment
  hierarchy; the nonzero formal top moment proves polynomial-domain
  minimality, not necessity for an entropy remainder, and tail cancellation
  prevents promoting it without new analysis.

## Selection

Route A, Johnson Open Problem 4, has the best probability-impact product
because the required flow is canonically present and both endpoints can be
closed. The proved result is explicitly the finite-variance Cauchy case, not
a solution of the full symmetric $\alpha$-stable problem. Problems 1 and 6
require machinery absent from the paper.
