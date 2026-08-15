# Arithmetic Criticality and Large Deviations for Fibonacci Partitions and Finite-Window Fibers

This directory contains the main manuscript `Arithmetic Criticality and Large
Deviations for Fibonacci Partitions and Finite-Window Fibers` and a separately
compiled supplement. The submission target is the *Journal of Number Theory*.

## Scope

The finite Fibonacci representation frequencies of Sidorov--Vershik are the
subset-sum coefficients used here after the exact shift
\(F_j^{\mathrm{SV}}=F_{j+1}\). With the convention for the golden-ratio
Bernoulli convolution used in the paper, the pressure dictionary is

\[
P(t)=t\log 2-\tau_\mu(t)\log\varphi.
\]

The positive spectrum is attributed to Lau--Ngai, and the all-real spectrum
and negative first-order phase transition are attributed to Feng--Olivier and
Feng; Hu is cited for the early local-dimension theory. The all-real pressure
and frozen branch are recorded as finite-layer recovery and consistency
results.

The main contribution consists of:

- the exact indexing and normalization dictionary from the golden-ratio
  Bernoulli-convolution \(L^q\)-spectrum to Fibonacci partition layers;
- the arithmetic critical point, critical Gibbs law, and full finite-layer
  LDP on a single standard Fibonacci partition layer;
- the exact identification with Dushistova's fixed-digit-sum continuant sum,
  the endpoint correction of its printed leading coefficient from
  \(R_s+2R_s^2\) to \(2R_s^2\), a simplified one-large-partial-quotient proof,
  and the critical renewal/Fibonacci transfer;
- the joint generation-cost and log-multiplicity LDP, including its affine
  two-dimensional coexistence face;
- the residue and affine fiber correspondence;
- the pointwise Fibonacci partition-difference formula;
- the exact two-layer interval identity and transferred extremal theorem;
- the uniform Weinstein layer-count lemma and the finite-layer recovery of the
  known negative-temperature frozen branch;
- the second-order critical finite-size laws, with the noninteger
  (m^{3-\sigma_0}) correction, and the uniform critical coexistence limit;
- the full real-tilt large deviation principle across the freezing corner;
- the exact finite-prime-support coefficient interface and the explicit
  heavy-cost obstruction at the active cutoff.

The conditional microcanonical refinements, exact dyadic ray, integer moment
transfer, direct quadratic recurrence, and high-tilt consequences are in
`supplement.pdf`, not in the main theorem spine.

The fixed finite-prime-support result is an exact rational generating-function
interface only. No directional coefficient asymptotic or quenched-velocity
law is asserted.

The arithmetic priority line is explicit: Moshchevitin--Zhigljavsky are the
global Farey-tree predecessor, and Dushistova previously treated the identical
local sum and its polynomial order. The manuscript's arithmetic novelty claim
is limited to the leading-constant correction and simplified proof; the
critical cost tail, stable law, and finite-size terms are downstream transfers
from that corrected local input.

The affine fiber--partition correspondence is stated for \(m\ge1\). In the
generic maximizing-residue formulas, \(I_{2k+1}\) is defined for \(k\ge5\),
whereas \(I_{2k}\) and \(J_{2k}\) are defined for \(k\ge7\); exceptional
initial cases are listed separately.

## Build

The bibliography is written directly in `sec_references.tex`; BibTeX is not
used. Compile the main article before the supplement so `xr-hyper` can resolve
cross-document references:

```powershell
latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error supplement.tex
```

The expected outputs are `main.pdf` and `supplement.pdf`.
