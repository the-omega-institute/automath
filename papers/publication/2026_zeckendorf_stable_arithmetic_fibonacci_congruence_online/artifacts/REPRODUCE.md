# Reproduction

The article's claims are proved analytically in the manuscript. The exact
finite calculations below are consistency checks for the multiplication-delay
witness and its supporting lemma; they are not premises of the theorem.

Set the working directory to

    papers/publication/2026_zeckendorf_stable_arithmetic_fibonacci_congruence_online/

and use an installed Python 3 interpreter through the command name `python`.
Do not substitute `python3` without first checking that it is a real
interpreter: on some setups that name resolves to a stub and the script
produces no output.

## Multiplication-delay witness

Run:

    python artifacts/verify_multiplication_delay_bound.py

The script checks the theorem's witness for every `n = 3,...,24`. The
recorded output included

    witness check, n = 3..24
        n= 3: admissible True, differ only at position 1 True, values exact True, outputs differ at some k>=n True
        n= 4: admissible True, differ only at position 1 True, values exact True, outputs differ at some k>=n True
        n= 5: admissible True, differ only at position 1 True, values exact True, outputs differ at some k>=n True
        n= 6: admissible True, differ only at position 1 True, values exact True, outputs differ at some k>=n True
        n=23: admissible True, differ only at position 1 True, values exact True, outputs differ at some k>=n True
        n=24: admissible True, differ only at position 1 True, values exact True, outputs differ at some k>=n True
      -> PASS

It then exhaustively checks the supporting finite-window lemma for
`n = 3,...,19` and printed

    supporting lemma, n = 3..19
        admissible words on positions 1..n-1 attain exactly F_(n+1)-1: 0 violations
      -> PASS

The command ended with

    Outputs must agree at every k >= 2 + delta_n; they differ at some k >= n;
    therefore 2 + delta_n > n, that is delta_n >= n - 1.

and exited with status 0.

The supported theorem is specifically for a most-significant-digit-first
machine at effective resolution `n`, reading padded synchronous inputs, whose
output coordinates at positions at least `i + delta_n` are irrevocably
determined after input position `i` is read, and which computes the stable
product for every pair in `X_n x X_n`. Under those hypotheses the conclusion
is `delta_n >= n - 1` for `n >= 3`. The bound must not be stated without the
scan model, quantifiers, and range.

## Theorem-level negative control

Run:

    python artifacts/verify_multiplication_delay_bound.py --negative-control

The switch changes only the claimed delay bound from `delta_n >= n - 1` to
the incorrect `delta_n >= n`. It does not alter the Fibonacci recurrence,
Zeckendorf conversion, witness inputs, loop ranges, admissibility test,
product values, output comparison, or supporting-lemma enumeration.

The witness check for every `n = 3,...,24` still printed `PASS`, and the
supporting lemma for every `n = 3,...,19` still printed `0 violations` and
`PASS`. The final lines were

    Outputs must agree at every k >= 2 + delta_n; they differ at some k >= n;
    therefore 2 + delta_n > n, that is delta_n >= n - 1.
    CLAIM CHECK  witness implication supports delta_n >= n: FAIL

The command also began by naming the mutation explicitly:

    NEGATIVE CONTROL  claimed delay bound: delta_n >= n - 1 -> delta_n >= n

It exited with status 1. The unchanged witness and lemma checks therefore
separate rejection of the wrong claimed bound from corruption of the
computational machinery.
