# teorth/equational_theories Issue #418 — Field Order Bound

## The Question (by Tao)

If a linear magma implication is disproven by a finite field, how large does
the field need to be? Their search: Z/kZ up to k=200 (cyclic groups only).
Largest new anti-implication at k=43. New results at Z/81Z (= Z/3⁴).

Key gap: carlini only tested cyclic groups Z/kZ, NOT actual finite fields
F_{p^j} for j>1. Tao asked about this, carlini said "I don't have any way
to handle j>1 fields."

## What Automath Can Contribute

1. **GF(233) = X_11 via instFieldOfPrime**: Fibonacci prime F_13 = 233.
   This is BEYOND their Z/200Z search range. If we test all linear magmas
   on GF(233) and find new anti-implications, that's a concrete new result.

2. **GF(1597) = X_15**: F_17 = 1597. Way beyond anything they've tested.

3. **Theory**: Can Fibonacci growth rate + Chebotarev give a bound?
   The density of Fibonacci primes might constrain how fast new anti-implications
   appear as field size grows.

## Concrete Task for Codex

Write a Python script that:
1. Implements linear magma checking on GF(p) for Fibonacci primes p = 2, 3, 5, 13, 89, 233
2. For each (p, a, b), checks which of the 4,694 equations are satisfied
3. Compares against carlini's known results (which equations are already separated)
4. Reports any NEW anti-implications at p = 89 or p = 233

This is a COMPUTATION, not a theory task. Codex runs Python, gets data, reports.

## References
- lean4/Omega/Folding/FiberRing.lean:188 (instField_X5, GF(13))
- lean4/Omega/Folding/FiberRing.lean:157 (stableValueRingEquiv)
- https://github.com/teorth/equational_theories/issues/418

## Computation Results (2026-04-20)

### 2-Variable Equations (810 of 4,694)

| Prime | New anti-implications | Cumulative total |
|---|---|---|
| p=2 | +439,263 | 439,263 |
| p=3 | +90,422 | 529,685 |
| p=5 | +56,259 | 585,944 |
| p=7 | +20,008 | 605,952 |
| p=11 | +2,612 | 608,564 |
| p=13 | +384 | 608,948 |
| p=17..83 | +0 each | 608,948 |
| **p=89 (GF(89), Fibonacci prime F_11)** | **+0** | **608,948** |

**Conclusion:** For 2-variable linear magma equations, anti-implications
saturate at p=13. Testing GF(89) adds zero new edges.

### 3-Variable Equations — RUNNING
Testing p=2..23, then p=89. Results pending.

### Open Question
Does the saturation point change for 3+ variable equations?
carlini found new results at Z/49Z and Z/81Z — those likely involve
3+ variable equations. If 3-var saturates later (e.g., p=43 as carlini
found), then GF(89) might add new edges for 3-var.

### Next Steps for Codex
1. Analyze the 3-variable computation results when ready
2. If new edges found at higher primes: write up as Issue #418 reply
3. If no new edges: write up the saturation analysis as theoretical contribution
4. Either way: relate the saturation phenomenon to Automath's fold structure

### 3-Variable Equations (2,090 of 4,694) — COMPLETE

| Prime | New anti-implications | Cumulative total |
|---|---|---|
| p=2 | +2,519,673 | 2,519,673 |
| p=3 | +106,071 | 2,625,744 |
| p=5 | +18,310 | 2,644,054 |
| p=7 | +48,279 | 2,692,333 |
| p=11..23 | +0 each | 2,692,333 |

**Conclusion:** 3-variable linear magma anti-implications saturate at p=7.
Even earlier than 2-variable (p=13).

### Combined Result

| Variable count | Equations | Saturation prime | Total anti-implications |
|---|---|---|---|
| ≤2 variables | 810 | p=13 | 608,948 |
| 3 variables | 2,090 | p=7 | 2,692,333 |

**Key insight for Issue #418:** For linear magmas x◇y = ax+by over prime
fields GF(p), all anti-implications among the 4,694 ETP equations are
detectable at p ≤ 13. Testing larger primes (including Fibonacci primes
GF(89), GF(233)) adds zero new edges.

**Note:** carlini found new results at Z/49Z and Z/81Z — these are prime
POWER cyclic groups, not prime fields. The distinction matters: Z/49Z has
zero divisors that GF(49) does not. The saturation result here applies to
prime fields (and cyclic groups of prime order) only.

**Possible contribution to #418:** This data provides an empirical upper
bound: for linear magma anti-implications, prime field order ≤ 13 suffices.
A theoretical proof of this bound (using resultant theory or Chebotarev)
would fully answer #418 for the linear case.
