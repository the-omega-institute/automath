# Finite-Window Zeckendorf Fibers

This directory contains the refocused manuscript
`Finite-Window Zeckendorf Fibers: Affine Partition Correspondence and
Negative-Temperature Freezing`.

## Scope

The compiled paper retains only the independently justified core:

- the residue and affine fiber correspondence;
- the pointwise Fibonacci partition-difference formula;
- the exact two-layer interval identity and transferred extremal theorem;
- the uniform Weinstein layer-count lemma and negative-temperature freezing;
- the precise compact-operator obstruction;
- the conditional real-tilt large deviation corollary;
- the integer moment transfer, direct quadratic recurrence, Sanna endpoint
  attribution, and diagonal high-tilt limit.

The invalid normalization transducer, collision automaton, histogram kernels,
arithmetic-window recurrence certificates, Galois computations, and
Chebotarev claims have been withdrawn. Their section sources and certificate
package are not part of this directory.

## Build

The bibliography is written directly in `sec_references.tex`; BibTeX is not
used. Compile twice to stabilize references:

```powershell
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The expected output is `main.pdf`.
