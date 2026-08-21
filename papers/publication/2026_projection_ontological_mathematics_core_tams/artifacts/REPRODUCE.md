# Reproduction

The article's general claims are proved analytically in the manuscript. The
finite numerical calculations below are consistency checks and are not used as
premises of theorems. The exact modular-arithmetic and root-isolation checks
give machine-assisted proofs of finite claims about the displayed polynomials;
they do not replace the manuscript's general arguments. In particular,
finite-window recurrence agreement does not by itself prove the audited
all-`m` identification of those polynomials with the collision moments.

All commands below were run with Python 3.10.11 from the working directory

    papers/publication/2026_projection_ontological_mathematics_core_tams/

with NumPy, SymPy, and mpmath installed. SymPy emits a deprecation warning about
ordered comparisons with modular integers during the polynomial and Galois
checks. The warning is harmless: it does not signal a failed assertion, and the
affected commands exit with the statuses stated below.

## Direct sequence generation

From the article directory specified above, run:

    python artifacts/generate_sequence_data.py

The script constructs the residue-count vector modulo `F_(m+2)` directly for
every `m = 0,...,26`, computes the exact moments `S_q(m)` for `q = 9,...,17`,
checks the displayed recurrences on that finite window, and records the initial
Hankel ranks and determinants. It rewrites
`artifacts/sequence_data_q9_17.json`.

Expect the progress lines to begin with `m= 0 modulus=1` and end with
`m=26 modulus=317811`, followed by

    wrote=...\artifacts\sequence_data_q9_17.json
    sha256=e7293d194a9414bd6b1b1a1b147ebf9aa41082cf9b6a1a1752fa3f539bb0594b

and exit status 0. The hash is from the recorded run. A reader may conclude
that the archived moments, finite-window recurrence checks, and initial-data
minimality checks are reproducible through `m = 26`. This does not prove that
the recurrences hold for every `m`.

## Partition-difference check

From the same article directory, run:

    python artifacts/verify_partition_difference.py

All enumeration in this script is exact integer arithmetic. `CONTROL 1`
brute-forces all binary words for `m = 1,...,18` and establishes that the fibre
multiplicity is the coefficient of the truncated Fibonacci product, that its
value range is exactly `[0,F_(m+2)-1]`, and that the total multiplicity is
`2^m`. `CONTROL 2` independently enumerates distinct Fibonacci subsets and
checks `R(n)` through `n = 200`; it prints

    R(0..10) = [1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2]

Both controls must print `PASS`. If either fails, the
`CONTROLS FAILED - stopping.` guard exits before any theorem-facing output.

The main exact check then tests the partition-difference identity for every
`m = 1,...,24` and every admissible `n`. Expect

    m = 1..24, 317808 values of n checked, 0 mismatches
  -> PASS

The finite asymptotic checks end with `D_30 = 1597`,
`D_30^(1/30) = 1.278724042`, pressure slopes
`[0.211935, 0.215593, 0.218178, 0.220131]`, and

    SUMMARY {'partition difference': True, 'D_m^(1/m)': True, 'convex pressure': True}

with exit status 0. The exhaustive range is an exact instance check of the
partition identity. The maximum-fibre limit and pressure output are finite-size
consistency checks for the analytic results.

## Maximum-fibre sibling check

From the same article directory, run:

    python artifacts/verify_max_fibre_matches_sibling.py

The script independently constructs the sibling paper's modular fibres for
`m = 1,...,18`. It compares their maxima with the closed formula and, through
`m = 10`, with the sibling's printed values; it also checks that every fibre
total is `2^(m+1)`. Expect every row to end in `ok` and

    single_primitive verified: True

It then compares the two conventions for `m = 2,...,15`. Each row has
`M_m(single_primitive) = D_{m+1}(projection)`; the final values are both `55`.
The command exits with status 0. A reader may conclude that the two exact
finite constructions have the claimed index-shift correspondence throughout
the checked range.

## Second-moment sibling check

From the same article directory, run:

    python artifacts/verify_moments_match_sibling.py

This script checks the sibling's exact `S_2` recurrence from independently
constructed modular fibres through `m = 21`, compares its characteristic root
with the projection moment ratios, and applies the rational-root test to the
cubic. Expect

    S_2(1..6) brute = [6, 14, 36, 88, 220, 544]
    recurrence holds for m=4..21: True   violations: []
    dominant root of x^3-2x^2-2x+2 = 2.481194304092
    difference at m=25: 5.403e-09
    f(+-1), f(+-2) = [-1, 1, -2, -10]  -> no rational root: True

and exit status 0. The recurrence comparison is exact on the stated range, the
root-ratio comparison is numerical, and the absence of a rational root proves
that the displayed cubic is irreducible over `Q`.

## Per-step rule defect

From the same article directory, run:

    python artifacts/verify_per_step_rule_defect.py

With fixed seed `3`, the script generates twelve bounded terminal-output
transducers and counts pairs whose completed outputs collide although their
per-step emissions differ. Expect

    totals: colliding pairs 1548, of which the per-step rule rejects 1155  (74.6 percent)

and the explicit witness

    inputs 000101 and 100111
    completed outputs both '010101'  -> they DO collide
    per-step emissions ['', '0', '', '1', '0', '1'] vs ['01', '0', '', '1', '', '']  -> the old rule rejects the pair

with exit status 0. This provides a concrete counterexample to literal
per-step equality as a collision test; it is not a statistical claim about all
transducers.

## Polynomial certificates and negative control

From the same article directory, run the unmutated certificate check:

    python artifacts/verify_polynomial_certificates.py

For every displayed `Pi_q`, `q = 9,...,17`, the script reduces the exact
integer polynomial at three certificate primes. It rejects a ramified prime by
raising `AssertionError`, asserts all 27 factorisation-degree patterns, checks
the exact Legendre-symbol values for `q = 12,...,15`, and asserts
`rank_mod_two == 4`. It writes the exact factors and discriminants to
`artifacts/polynomial_certificates_q9_17.json`. Expect

    verified_polynomials=9
    verified_modular_factorizations=27
    verified_discriminant_binary_rank=4
    wrote=...\artifacts\polynomial_certificates_q9_17.json
    sha256=7ff8b160b245374a5a6f4bc23f195f27f0937a67e6f03f89ef84c196cbbdbda9

and exit status 0. This hash is from the unmutated recorded run. These are exact
finite-field, discriminant, and binary-rank certificates for the displayed
polynomials, not numerical indications.

The theorem-level negative control is:

    python artifacts/verify_polynomial_certificates.py --negative-control

It changes only the claimed coefficient of `x^5` in `Pi_9` from `-62` to
`-61`. It does not alter sequence generation, recurrence code, loop bounds,
indices, certificate primes, factorisation logic, the other eight polynomials,
Legendre values, or binary-rank computation. Expect

    NEGATIVE CONTROL  claimed Pi_9 coefficient of x^5: -62 -> -61
    computed_polynomials=9
    computed_modular_factorizations=27
    verified_discriminant_binary_rank=4
    CHECK  modular certificates for unmodified Pi_10..Pi_17: PASS
    CHECK  discriminant Legendre values and rank_mod_two == 4: PASS
        Pi_9 prime=17: expected degrees=[6, 1], observed=[7]
        Pi_9 prime=13: expected degrees=[3, 2, 1, 1], observed=[4, 2, 1]
    CLAIM CHECK  modular certificates for mutated Pi_9: FAIL

and exit status 1. The mutated payload has a different hash and is not written;
the hash quoted above is only for the unmutated recorded run. The unaffected
modular, Legendre-symbol, and rank controls still pass, while only the
certificate claim for the altered `Pi_9` fails. This shows that the verifier
rejects an incorrect asserted polynomial coefficient without corrupting its
mathematical machinery or the canonical JSON artifact.

## Minimal-polynomial premise

After an unmutated polynomial-certificate run, from the same article directory
run:

    python artifacts/verify_minimal_polynomial_premise.py

Part (a) recomputes `S_q(m)` from the fibre definition through `m = 28` and
checks the displayed recurrences in exact integer arithmetic. Expect, for
`q = 9,...,17`, respectively,

    21, 19, 19, 15, 17, 15, 17, 15, 15 exact matches, no failures
  -> PASS

Part (b) independently applies the distinct-degree irreducibility criterion at
the first certificate prime for each polynomial. Expect every row to say
`irreducible`, every certificate comparison to say `agree True`, and a second
`PASS`, followed by

    Both halves hold, so Pi_q is the minimal polynomial of lambda_q and not merely a
    factor of a larger characteristic polynomial. The premise of the Galois section
    is independently confirmed.

The command exits with status 0. The modular irreducibility conclusions are
exact. The recurrence computation confirms the premise on the independently
computed finite range; the manuscript separately records the condition needed
to identify the recurrence with the infinite sequence.

## Sanna table continuation

From the same article directory, run:

    python artifacts/verify_sanna_table_continuation.py

The opening `CONTROL` recomputes the largest real roots of Sanna's printed
polynomials for indices `1,...,8` and compares them with his printed decimal
values. Expect all eight rows to end in `ok` and the control to print `PASS`.
This establishes that the transcription and root-selection convention agree
before the continuation is examined.

The continuation appends the displayed rows `9,...,17`, normalises each root by
its index, and checks the leading polynomial pattern. Expect the normalised
values to decrease from `1.4559219` at index 3 to `1.2872439` at index 17,
followed by

    target sqrt(phi) = 1.2720196
  monotone decreasing past index 2 -> PASS
  ratio lambda_9 / lambda_8 = 1.2532003, in line with the neighbouring ratios -> the rows are consecutive

  every polynomial in both families begins X^d - 2X^(d-1) -> PASS

and exit status 0. This is a numerical consistency check that the displayed
rows continue Sanna's table and have the stated common leading pattern.

## Sanna Galois groups

From the same article directory, run:

    python artifacts/verify_sanna_galois_groups.py

This is a machine-assisted proof, not a numerical indication. Irreducibility
and modular factorisations are exact. Dedekind's theorem turns the exact
factorisation degrees modulo an unramified prime into Frobenius cycle types.
For degree 7, prime degree gives primitivity, a 3-cycle and Jordan's theorem
give `A_7`, and an odd cycle type gives `S_7`. For degree 9, a 5-cycle with
`5 > 9/2` gives primitivity, `5 <= 9-3` and Jordan's theorem give `A_9`, and an
odd cycle type gives `S_9`. Degrees 3 use the exact discriminant test, and
degrees 5 use SymPy's exact degree-at-most-six Galois algorithm.

Expect the rows for Sanna indices `2,...,8` to report, in order,
`S_3, S_3, S5TransitiveSubgroups.S5, S5TransitiveSubgroups.S5, S_7, S_7,
S_9`, followed by

    every one of Sanna's rows is the full symmetric group: True

and exit status 0. A reader may conclude rigorously that every polynomial in
Sanna's own Table 1 covered by the command has full symmetric Galois group.
Together with the exact `q = 9,...,17` Frobenius patterns checked by the
polynomial verifier, this also shows that the paper's full-symmetric outcomes
continue an existing generic pattern rather than breaking one.

## Secondary-root separation

From the same article directory, run:

    python artifacts/verify_secondary_spectrum.py

Using rational endpoints, exact Cauchy root counts, squarefreeness, and SymPy's
complex-root isolation, this script certifies one negative real root, one
larger positive Perron root, and a strict modulus bound for every remaining
root of each displayed polynomial. Expect

    q real nonreal max_other certified_gap
     9    3       4  5.807036      1.258295
    10    3       6  7.686463      1.413679
    11    5       4 10.074257      1.638682
    12    7       6 13.109659      1.957050
    13    7       4 16.968010      2.401961
    14    7       6 21.870527      3.018835
    15    7       4 28.096494      3.869169
    16    7       6 35.998557      5.035680
    17    7       6 46.022001      6.629059
    minimum_certified_gap=1.258295

and exit status 0. The printed decimals summarize exact rational isolating
bounds; the strict root ordering and modulus separation are certified rather
than inferred from floating-point approximations.

## Automated negative-control check

From the same article directory, run:

    python -m unittest discover -s artifacts -p "test_*.py" -v

The test executes the polynomial verifier with `--negative-control` and
requires exit status 1, the explicit coefficient mutation, passing verdicts
for the unaffected checks, and a failing verdict for the mutated `Pi_9` claim.
Expect

    test_negative_control_rejects_one_wrong_pi_9_coefficient (test_polynomial_certificates.PolynomialCertificateTest) ... ok

    ----------------------------------------------------------------------
    Ran 1 test

    OK

with exit status 0. This confirms that the negative-control failure mode
remains executable and machine-checked.
