# Context-free rigidity in recurrent numeration

This directory contains the Monatshefte fuer Mathematik article and its
deterministic consistency checks. The article is mathematically self-contained;
the finite-state results developed separately are not part of this submission.

## Reproducibility

Run all commands from this directory. Full commands and file roles are in
`REPRODUCE.md`; the upload manifest is in `submission_metadata.md`.

The deterministic verifier is expected to report:

- systems checked: 6;
- affine action cases: 2282;
- valid canonical pump witnesses: 5;
- synchronized orbit cases: 159;
- inflated Fibonacci cases: 1418;
- tail-prefix action cases: 63;
- geometric ray cases: 13;
- linear Perron classification cases: 6;
- weak-Perron radical cases: 18;
- length-order-free selection cases: 1;
- geometric-ratio and Evertse support cases: 4 each;
- every recorded failure count: 0;
- final status: `OVERALL: PASS`.

The unit-test archive must report 21 tests and `OK`. The verifier contains
exact expected totals and exits nonzero if any archived count drifts. Neither
script uses the network or randomness.
