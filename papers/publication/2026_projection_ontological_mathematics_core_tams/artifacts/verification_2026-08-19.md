# Independent check of the partition-difference foundation — projection, 2026-08-19

Script: `verify_partition_difference.py`, in this directory.

Everything in this 47-page paper rests on one theorem: the fibre multiplicities are
Fibonacci-lag discrete derivatives of the classical Fibonacci partition function,

    d_m(n) = R+(n) - R+(n - F_{m+1})        for 0 <= n < F_{m+2},   R+(n) = R(n) + R(n-1).

If that fails, the squeeze on `S_q(m)`, the algebraicity of each `lambda_q`, the pressure
bands and the limit `D_m^{1/m} -> sqrt(phi)` all fail with it. So that is what was checked.

## Controls

- **The setup reading.** By brute force over all of `{0,1}^m` for `m = 1..18`, the number of
  words with `sum omega_j F_j = n` equals `[z^n] prod_{j=1}^m (1 + z^{F_j})`, the value range
  is exactly `[0, F_{m+2}-1]`, and the totals are `2^m`. So the fibre multiplicity really is
  that coefficient and no modular reduction enters.
- **`R(n)`.** Independent subset enumeration agrees to `n = 200`. The initial values
  `1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2` are the standard Fibonacci-representation counts.

## The theorem

Checked exhaustively for `m = 1..24`, every `n` in range: **317,808 values, zero
mismatches.** The foundation holds.

## The asymptotics built on it

- `S_1(m+1)/S_1(m) = 2.000000000` exactly, as it must be.
- `lambda_2 = 2.4811943`, `lambda_3 = 3.0861302`, `lambda_4 = 3.8460593`, stable to seven
  digits between `m = 20` and `m = 25`.
- Pressure `p_q = log lambda_q` with `p_0 = log phi`: slopes `0.211935, 0.215593, 0.218178,
  0.220131`, nondecreasing. **Convexity confirmed.**

## A finding: the maximal fibre has an exact closed form

The paper proves `D_m^{1/m} -> sqrt(phi)` through a zero-temperature tilt argument. The
maximum is in fact exactly a Fibonacci number, on both parity classes:

    m even :  D_m = F_{m/2 + 2}
    m odd  :  D_m = 2 F_{(m+1)/2}

verified for every `m = 6..32` — `F_5, F_6, ..., F_18` on the even side, and
`6, 10, 16, 26, 42, 68, 110, 178, 288, 466, 754, 1220, 1974 = 2F_4, 2F_5, ..., 2F_16` on the
odd side.

This is **sharper than the stated limit** and explains the whole approach curve. From
`F_k ~ phi^k / sqrt5`, the even branch gives

    D_m^{1/m} = sqrt(phi) * phi^{2/m} * 5^{-1/(2m)} * (1 + o(1)),

which matches the computed values to **nine digits** — at `m = 32`, `1.278303979` against a
predicted `1.278303981`. The odd branch carries an extra factor `(2/sqrt5)^{1/m} < 1`, which
is exactly the even-odd oscillation visible in the table.

So the residual of about `6.7e-3` at `m = 30` is not a discrepancy but the predicted `1/m`
correction, of size `(2 log phi - (1/2) log 5)/m = 0.158/m`.

Stated as what it is: a pattern verified over `m = 6..32`, not a proof. But it is a clean
statement, it implies the paper's limit immediately, and it supplies the second-order term
the paper does not currently give. Worth putting to the authors.

---

# Addendum, next day: the closed form is already proved next door

The maximal-fibre closed form recorded above as "a pattern, not a proof" is a theorem in a
sibling manuscript. `single_primitive` states and proves

    M_{2s-1} = F_{s+1},   M_{2s} = 2 F_s        (its convention F_1 = 1, F_2 = 2)

and the two papers are computing the same sequence with an index shift of one:

    D_{m+1}  (projection)  =  M_m  (single_primitive),     verified for m = 2..15.

So `projection` can cite its sibling and replace `D_m^{1/m} -> sqrt(phi)` with the exact
value, which carries the second-order term for free. That upgrade costs a citation and a
sentence. Script: `verify_max_fibre_matches_sibling.py`.

`single_primitive`'s formula was itself checked here: brute force agrees for `m = 1..18`,
its own tabulated `M_1..M_10 = 2,2,3,4,5,6,8,10,13,16` agree, and the fibre totals come to
`2^{m+1}` at every `m`, which confirms the residue classes are being counted completely.

## The mistake I made getting here, because it has a reusable tell

My first model of `single_primitive`'s fold left out the modular reduction. Its weights sum
past `F_{m+2}`, so its fibres are whole residue classes; `projection`'s weights sum to
exactly `F_{m+2} - 1`, so its fibres are single coefficients and no reduction occurs. With
the wrong model, brute force disagreed with `single_primitive`'s formula at almost every
`m`, and it would have been easy to write that up as an error in a submitted paper.

The tell was in the output: **the paper's formula agreed exactly with the paper's own
tabulated values, and only my recomputation dissented.** A document consistent with itself
while disagreeing with an outside model indicts the model. That is worth checking before
reporting any formula as wrong.

---

# Addendum: the two papers compute the same sequences

Following the maximal-fibre correspondence one step further. For `q = 1, 2, 3, 4` and
`m = 1..12`,

    S_q(m+1)  (projection)  =  S_q(m)  (single_primitive)      exactly,

alongside `D_{m+1} = M_m` for the maxima. The two manuscripts are studying **one fold under
two conventions**, differing by an index shift of one. The conventions hide it: this paper's
weights sum to exactly `F_{m+2} - 1` so its fibres are single coefficients, while the
sibling's weights sum past `F_{m+2}` so its fibres are whole residue classes. Those are
different constructions that produce identical numbers.

Script: `verify_moments_match_sibling.py`.

## What this paper can take from the sibling

- **The maximal fibre**, exactly, instead of `D_m^{1/m} -> sqrt(phi)`.
- **The minimal polynomial of `lambda_2`.** The sibling's exact recurrence
  `S_2(m) = 2S_2(m-1) + 2S_2(m-2) - 2S_2(m-3)` — verified here against brute force for
  `m = 4..21`, initial values `6, 14, 36, 88, 220, 544` — has characteristic polynomial
  `x^3 - 2x^2 - 2x + 2`, whose dominant root is `2.481194304092`. That is `lambda_2`: this
  paper's ratios `S_2(m+1)/S_2(m)` reach it to `5.4e-9` by `m = 25`. The cubic is monic with
  constant term 2, so the only rational-root candidates are `+-1, +-2`, and `f` takes values
  `-1, 1, -2, -10` there. It is therefore irreducible, and

      lambda_2 is an algebraic integer of degree exactly 3, with minimal polynomial
      x^3 - 2x^2 - 2x + 2.

  This paper currently says only that each `lambda_q` is the Perron root of some nonnegative
  integer matrix and hence an algebraic integer. For `q = 2` the sibling supplies the
  polynomial and the exact degree.

## The disclosure question

Neither manuscript mentions the other. Checked in both directions across every `.tex` and
`.bib`, with a control confirming the search works — both cite Sanna, 17 hits here and 4
there.

Two submissions computing identical sequences, from the same authors, need to say so in each
other's presence. This is not duplication: the results genuinely differ — this paper has the
higher-`q` Perron structure, the pressure bands and the Galois audit; the sibling has the
exact recurrence and the exact fibre maxima. They are complementary treatments of one
object, which is a perfectly good thing to be, and is exactly what should be stated. Whether
they are better as one paper is the authors' call, not mine. What is not an option is
sending both out silent about each other, in a small field with overlapping referee pools.

This is the third instance of the same pattern this week, after the Berstel adder missing
from `zeck_arith` and Ostrowski missing from `folded_histograms`: the project already owns
the result, in the manuscript next door.
