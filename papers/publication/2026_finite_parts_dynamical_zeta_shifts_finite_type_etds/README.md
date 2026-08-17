# Linear radial determination

This directory builds two related papers.

- 'main.tex' is the inverse-theorem manuscript. Its principal theorem concerns
  relatively unit-Adams-invariant pairs of extensions by a finite abelian
  prime-power group. For primitive bases of sizes 'v' and 'v'', equality of
  the primitive data through length 'L' and equality of the full
  element-profile vector at 'K' distinct radii, one algebraic, recover all
  primitive length-element data when K + L >= max(v, v').

  In particular, 'V' radial locations suffice for bases of size at most 'V',
  independently of the group rank and exponent. A common-base binary family
  gives the complementary linear lower bound, so the universal binary radial
  determination number is 'Theta(V)'.

- 'supplement.tex' contains the Adams-corrected Frobenius-class product
  constant, quotient-cover refinements, and the exact strict-gap 'S3'
  witness. These results are logically separate from the inverse theorem.

The inverse theorem is unconditional. The critical nonlinear Mahler step is
reduced to the verified linear rational-transcendental dichotomy by
logarithmic differentiation; a power-map divisor congruence then removes
finite monodromy. The manuscript also proves a sharp squarefree certificate
bound, a collision-jet inequality, a sharp-order 'O(D log D)' total-degree
bound with effective height and bit estimates, and realizable binary and
odd-prime collision families.

The radii lie in the common open Perron interval. A strict twisted gap is
required only for the binary endpoint extension. No finite polynomial
sampling bound is claimed for every finite group: already outside the
relative unit-Adams-invariant 'C3' class, Adams-Mobius inversion produces a
coupled cyclotomic Euler system not covered by the one-variable method.

Build and exact-verification commands are recorded in 'REPRODUCE.md'.
