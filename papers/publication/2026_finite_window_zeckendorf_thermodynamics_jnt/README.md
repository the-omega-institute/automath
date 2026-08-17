# Finite-Window Zeckendorf Thermodynamics

This directory contains the main article and its separately compiled
technical appendix. The primary submission target is the *Journal of Number
Theory*.

The article studies exact finite-window Fibonacci coefficient spectra. Its
main results are the affine coefficient-spectrum correspondence, the
pointwise partition-difference formula, the exact two-layer identity, the
second-largest fiber classification, sharp local stabilization, the
mesoscopic power-law spectrum, critical finite-window Gibbs and coexistence
laws, and the completion of the large-deviation principle across the
freezing corner. Pressure formulas
from the golden-ratio Bernoulli-convolution literature and the transferred
extremal classification are used as subordinate inputs, with their provenance
stated in the manuscript.

The companion article, *Brocot Condensation and Critical Fibonacci Renewal*,
contains the total-variation condensation law, the corrected scalar
denominator-layer asymptotic, and the arithmetic critical renewal
consequences.

## Build

The bibliography is written directly in `sec_references.tex`; BibTeX is not
used. Build the main article before the appendix so `xr-hyper` can resolve
cross-document references:

```powershell
latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error supplement.tex
```

The expected outputs are `main.pdf` and `supplement.pdf`. Reproduction
commands for the computational checks are in `artifacts/REPRODUCE.md`.
