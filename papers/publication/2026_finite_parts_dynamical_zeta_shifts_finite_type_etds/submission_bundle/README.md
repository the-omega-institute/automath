# Finite radial determination for binary SFT extensions

This directory builds two related papers.

- `main.tex` is the inverse-theorem manuscript. Its spine is the effective
  finite radial sampling theorem for same-base `C2` extensions without a
  twisted-gap hypothesis in the open Perron interval, the exact determinant
  lifting theorem, and the explicit obstruction to
  extending the method to arbitrary finite groups.
- `supplement.tex` contains the Adams-corrected Frobenius-class product
  constant, quotient-cover refinements, and the exact strict-gap `S3`
  witness. These results are logically separate from the inverse theorem.

The proved uniform sampling budget in the main paper is

```text
B(v,C2) = (2v)^2 (2^(floor(log2(2v))+1) - 1) < 16 v^3.
```

The budget is unconditional for algebraic radii in
`0 < y < lambda^(-1)`. A strict twisted gap is required only to admit the
endpoint `y = lambda^(-1)`. In the binary case the determinant ratio used by
the algorithm is exactly the ratio of the ordinary Artin-Mazur zeta functions
of the two standard covers.

No finite polynomial sampling bound is claimed for every finite group. The
paper locates the obstruction already at `C3`: Adams--Mobius inversion has
non-lacunary support and produces a coupled cyclotomic Euler system for which
the required special-value and effective zero theorems are not available.

Build and exact-verification commands are recorded in `REPRODUCE.md`.
