# Finite radial determination for binary SFT extensions

This directory builds two related papers.

- `main.tex` is the inverse-theorem manuscript. Its spine is the effective
  finite radial sampling theorem for same-base `C2` extensions, the exact
  determinant-boundary lifting theorem, and the explicit obstruction to
  extending the method to arbitrary finite groups.
- `supplement.tex` contains the Adams-corrected Frobenius-class product
  constant, quotient-cover refinements, and the exact strict-gap `S3`
  witness. These results are logically separate from the inverse theorem.

The proved uniform sampling budget in the main paper is

```text
B(v,C2) = (2v)^2 (2^(floor(log2(2v))+1) - 1) < 16 v^3.
```

No finite polynomial sampling bound is claimed for every finite group. The
paper locates the obstruction already at `C3`: Adams--Mobius inversion has
non-lacunary support and produces a coupled cyclotomic Euler system for which
the required special-value and effective zero theorems are not available.

Build and exact-verification commands are recorded in `REPRODUCE.md`.
