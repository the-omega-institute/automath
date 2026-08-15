# Finite radial determination for abelian two-group SFT extensions

This directory builds two related papers.

- `main.tex` is the inverse-theorem manuscript. Its spine is finite radial
  determination for odd-Adams-invariant extensions by arbitrary finite
  abelian 2-groups over possibly different bases, without a twisted-gap
  hypothesis in the open Perron interval. It also contains the parity-free
  rational critical Mahler lifting theorem, effective certificate bounds,
  and realizable lower-bound families on standard `C2` covers.
- `supplement.tex` contains the Adams-corrected Frobenius-class product
  constant, quotient-cover refinements, and the exact strict-gap `S3`
  witness. These results are logically separate from the inverse theorem.

For base matrices of size at most `V`, the proved uniform sampling budget is

```text
M(V) = 2 V ceil(log2(4V)).
```

The radii lie in the common open Perron interval and at least one is
algebraic. A strict twisted gap is required only for the binary endpoint
extension. The theorem is automatic for elementary 2-groups and covers
genuine higher 2-power holonomy under odd-Adams invariance. A standard-cover
family gives an `Omega(V)` sampling lower bound, while a separate realizable
family shows that the `O(D log D)` Mahler certificate-degree bound has the
correct order.

No finite polynomial sampling bound is claimed for every finite group. The
paper locates the obstruction already at `C3`: Adams--Mobius inversion has
non-lacunary support and produces a coupled cyclotomic Euler system for which
the required special-value and effective zero theorems are not available.

Build and exact-verification commands are recorded in `REPRODUCE.md`.
