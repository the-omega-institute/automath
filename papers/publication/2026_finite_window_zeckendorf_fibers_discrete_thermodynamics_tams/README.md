# Fibonacci Partition Thermodynamics and Finite-Window Zeckendorf Fibers

This directory contains the refocused main manuscript
`Fibonacci Partition Thermodynamics and Finite-Window Zeckendorf Fibers` and
a separately compiled supplement.

## Scope

The compiled paper retains only the independently justified core:

- the all-real pressure, critical Gibbs law, and full LDP on a single
  standard Fibonacci partition layer;
- the joint generation-cost and log-multiplicity LDP, including its affine
  two-dimensional coexistence face;
- the residue and affine fiber correspondence;
- the pointwise Fibonacci partition-difference formula;
- the exact two-layer interval identity and transferred extremal theorem;
- the uniform Weinstein layer-count lemma and negative-temperature freezing;
- the linear critical finite-size law and uniform critical coexistence limit;
- the precise compact-operator obstruction;
- the full real-tilt large deviation principle across the freezing corner;
- the exact finite-prime-support coefficient interface and the explicit
  heavy-cost obstruction at the active cutoff.

The conditional microcanonical refinements, exact dyadic ray, integer moment
transfer, direct quadratic recurrence, and high-tilt consequences are in
`supplement.pdf`, not in the main theorem spine.

The invalid normalization transducer, collision automaton, histogram kernels,
arithmetic-window recurrence certificates, Galois computations, and
Chebotarev claims have been withdrawn. Their section sources and certificate
package are not part of this directory.

## Build

The bibliography is written directly in `sec_references.tex`; BibTeX is not
used. Compile the main article before the supplement so `xr-hyper` can resolve
cross-document references:

```powershell
latexmk -pdfxe -interaction=nonstopmode -halt-on-error main.tex
latexmk -pdfxe -interaction=nonstopmode -halt-on-error supplement.tex
```

The expected outputs are `main.pdf` and `supplement.pdf`.
