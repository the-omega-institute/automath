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
