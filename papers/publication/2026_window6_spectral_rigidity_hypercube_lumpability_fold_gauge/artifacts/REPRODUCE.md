# Reproduction

The article's claims are proved analytically in the manuscript. The exact
finite computations below are consistency checks and auditable instances of
the partition and involution statements; they are not premises of the general
proofs. In particular, the finite sweeps do not replace the proved
preservation criterion or the cited Diophantine classification.

All commands below were run from the working directory

    papers/publication/2026_window6_spectral_rigidity_hypercube_lumpability_fold_gauge/

with Python 3. They use only the Python standard library.

## Exact window-6 partition checks

Run:

    python artifacts/verify_hidden_refinement.py
    python supplement/verify_window6_streams.py

The first command independently groups all 64 vertices by their neighbor
signatures, compares the resulting 48 cells with the orbits of
`sigma_geo`, checks that the cells partition all vertices, checks that each
orbit remains in one `Fold_6` fiber, verifies equitability, and verifies the
profile of 32 singleton cells and 16 two-vertex cells. It printed

    window6 hidden refinement certificate: all assertions passed

and exited with status 0.

The second command is part of the paper's supplement, rather than
`artifacts/`. It regenerates the canonical window-6 fiber, edge-count,
stabilizer, residual-witness, and stochastic-budget streams, checks their
SHA-256 values, and compares them byte-for-byte with
`supplement/window6_canonical_streams.txt`. It printed

    window6 canonical streams: all assertions passed

and exited with status 0. These are the two asserting Python verifiers among
the six commands documented here.

For the worked window, the original fold has 21 cells and its unique minimal
equitable refinement has 48 cells. The manuscript proves the quotient
spectrum multiplicities

    (1, 5, 11, 14, 11, 5, 1).

The two commands above audit the finite fold streams and the 48-cell
partition identities. They do not replace the manuscript's analytic
spectral-carrier argument.

## Dimension and mechanism enumerations

Run each command from the same paper root:

    python artifacts/verify_refinement_family.py
    python artifacts/verify_involution_mechanism.py
    python artifacts/verify_admissible_dimensions.py
    python artifacts/verify_preservation_criterion.py

`verify_refinement_family.py` performs the full equitable-refinement sweep
through `m = 16`. The recorded table included

      m  fold cells   refined                profile  discarded   2^(m-2)  match
      3           5         6           {1: 4, 2: 2}          2         2   True
      6          21        48         {1: 32, 2: 16}         16        16   True
      8          55       192        {1: 128, 2: 64}         64        64   True
      9          89       384       {1: 256, 2: 128}        128       128   True

and ended with

    m with a nontrivial refinement: [3, 6, 8, 9]

Thus the observed cell counts at the four dimensions are
`3 * 2^(m-2) = 6, 48, 192, 384`.

`verify_involution_mechanism.py` printed the four Fibonacci numbers below
`F_90` that are sums of two distinct powers of two,

    F_4 = 3 = 2^1 + 2^0
    F_5 = 5 = 2^2 + 2^0
    F_9 = 34 = 2^5 + 2^1
    F_12 = 144 = 2^7 + 2^4
    total below F_90: 4

and its table marked nontrivial refinements only at `m = 3, 6, 8, 9` in the
classified range `m >= 3`.

`verify_admissible_dimensions.py` streamed the candidate tests through
`m = 22` and ended with

    m admitting a fold-preserving swap-and-complement involution: [3, 6, 8, 9]

Its table contains candidate `(i,j)` pairs on every row through `m = 22`,
while the preserving-pair column is empty for every `m = 10,...,22`. This is
a built-in search control: the empty admissible column past 9 is a computed
result, not evidence that candidate generation or the sweep stopped.

`verify_preservation_criterion.py` compared brute force with the proved
criterion on every candidate for `2 <= m <= 16` and ended with

    candidates tested: 49   disagreements: 0

All four enumeration commands exited with status 0. They compute and print
tables for the reader to compare; they contain no assertions that
automatically certify the final classification. A clean process exit alone
must therefore not be mistaken for automatic confirmation of the
classification.

## Theorem-level negative control

Run:

    python artifacts/verify_hidden_refinement.py --negative-control

The switch changes only the claimed refinement cell count from 48 to the
incorrect value 47. It does not alter the vertex set, fold computation,
neighbor signatures, involution, orbit construction, adjacency tests, or
cell table. The command printed

    NEGATIVE CONTROL  claimed refinement cell count: 48 -> 47
    CHECK  neighbor-signature classes equal the claimed cell partition: PASS
    CHECK  sigma_geo orbits equal the claimed cell partition: PASS
    CHECK  claimed cells partition all 64 vertices exactly once: PASS
    CHECK  sigma_geo orbits remain inside Fold_6 fibers: PASS
    CHECK  sigma_geo orbit partition is equitable: PASS
    CHECK  orbit-size distribution is 32 singletons and 16 pairs: PASS
    CLAIM CHECK  refinement has 47 cells: FAIL (computed 48)

and exited with status 1. Thus every pre-existing mathematical check still
passes under mutation, while the one altered theorem-facing value is rejected.
