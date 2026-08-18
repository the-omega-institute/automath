#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent check of the two sharp thresholds in fibonacci_folding.

Section 5 states two thresholds and asserts both are sharp:

  Theorem (sharp block separation). For m >= 3, the folded-window map
  W_{m,L} : {0,1}^L -> X_m^{L-m+1} is injective when L >= 2m-1, and the threshold is
  sharp: distinct blocks of length 2m-2 share a folded-window sequence.

  Theorem (exact causal decoder). Any two lifts of the same three consecutive symbols have
  the same terminal digit, so a decoder on three labels exists; no decoder using only two
  labels recovers the terminal digit. The exact zero-anticipation memory is 2, independent
  of m.

Both are finite statements at each m and are checked here exhaustively, together with the
explicit witness pairs the paper displays.

Fold: N_m(omega) = sum_j omega_j F_{j+1} with F_0 = 0, F_1 = 1, then the first m digits of
the Zeckendorf expansion of that value.
"""
import sys
from itertools import product

FIB = [0, 1]
while len(FIB) < 60:
    FIB.append(FIB[-1] + FIB[-2])


def value(w):
    return sum(int(b) * FIB[j + 2] for j, b in enumerate(w))


def zeck_prefix(n, m):
    if n == 0:
        return "0" * m
    ks, rest, k = [], n, 2
    while FIB[k + 1] <= n:
        k += 1
    while rest > 0:
        while FIB[k] > rest:
            k -= 1
        ks.append(k)
        rest -= FIB[k]
        k -= 1
    out = ["0"] * m
    for k in ks:
        if 0 <= k - 2 < m:
            out[k - 2] = "1"
    return "".join(out)


def fold(w):
    return zeck_prefix(value(w), len(w))


def windows(w, m):
    return tuple(fold(w[i:i + m]) for i in range(len(w) - m + 1))


def words(n):
    for t in product("01", repeat=n):
        yield "".join(t)


# ---------------------------------------------------------------- controls

def control_two_letter():
    print("CONTROL 1  the two-letter fold table printed in the paper")
    want = {"00": "00", "10": "10", "01": "01", "11": "00"}
    ok = all(fold(k) == v for k, v in want.items())
    print("    " + "   ".join(f"{k}->{fold(k)}" for k in want))
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def control_bijection(maxm=14):
    print("CONTROL 2  N_m is a bijection from X_m onto {0,...,F_{m+2}-1}, and the fold "
          "fixes X_m")
    ok = True
    for m in range(1, maxm + 1):
        legal = [w for w in words(m) if "11" not in w]
        if sorted(value(w) for w in legal) != list(range(FIB[m + 2])):
            ok = False
            print(f"    MISMATCH at m={m}")
        if any(fold(w) != w for w in legal):
            ok = False
            print(f"    fold does not fix a legal word at m={m}")
    print(f"    m = 1..{maxm}: |X_m| = F_(m+2), values exhaust the interval, fold fixes X_m")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


# ---------------------------------------------------------------- theorem 1

def sharp_block_separation(mmax=9):
    print("THEOREM 1  injective at L = 2m-1, and NOT injective at L = 2m-2")
    ok = True
    for m in range(3, mmax + 1):
        L = 2 * m - 1
        seen = {}
        collide = None
        for w in words(L):
            k = windows(w, m)
            if k in seen:
                collide = (seen[k], w)
                break
            seen[k] = w
        inj = collide is None

        Lm = 2 * m - 2
        seen2, wit = {}, None
        for w in words(Lm):
            k = windows(w, m)
            if k in seen2:
                wit = (seen2[k], w)
                break
            seen2[k] = w
        not_inj = wit is not None

        good = inj and not_inj
        ok &= good
        print(f"    m={m:2d}  L={L:2d} injective over 2^{L} words: {inj}"
              f"   |  L={Lm:2d} has a collision: {not_inj}"
              f"   {'ok' if good else 'MISMATCH'}")
        if collide:
            print(f"        UNEXPECTED collision at L={L}: {collide}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def paper_witness(mmax=12):
    """u has a 1 at position m+1; v has 1s at positions m-1 and m; length 2m-2."""
    print("WITNESS  the sharpness pair displayed in the proof")
    ok = True
    for m in range(3, mmax + 1):
        L = 2 * m - 2
        u = ["0"] * L
        v = ["0"] * L
        u[m] = "1"                     # position m+1, one-indexed
        v[m - 2] = "1"                 # position m-1
        v[m - 1] = "1"                 # position m
        u, v = "".join(u), "".join(v)
        same = windows(u, m) == windows(v, m)
        ok &= same and u != v
        print(f"    m={m:2d}  u={u}  v={v}  same window sequence: {same}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


# ---------------------------------------------------------------- theorem 2

def causal_decoder(mmax=10):
    print("THEOREM 2  three labels determine the terminal digit; two labels do not")
    ok = True
    for m in range(3, mmax + 1):
        # three labels correspond to a lift of length m+2
        by3 = {}
        bad3 = False
        for w in words(m + 2):
            key = windows(w, m)
            d = w[-1]
            if key in by3 and by3[key] != d:
                bad3 = True
                break
            by3[key] = d
        # two labels correspond to a lift of length m+1
        by2 = {}
        bad2 = False
        for w in words(m + 1):
            key = windows(w, m)
            d = w[-1]
            if key in by2 and by2[key] != d:
                bad2 = True
                break
            by2[key] = d
        good = (not bad3) and bad2
        ok &= good
        print(f"    m={m:2d}  three labels well defined: {not bad3}"
              f"   |  two labels ambiguous: {bad2}   {'ok' if good else 'MISMATCH'}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def optimality_witness(mmax=12):
    """Length m+1 blocks: u_{m+1}=1 against v_{m-1}=v_m=1, same two labels, different digit."""
    print("WITNESS  the two-label ambiguity pair displayed in the proof")
    ok = True
    for m in range(3, mmax + 1):
        L = m + 1
        u = ["0"] * L
        v = ["0"] * L
        u[m] = "1"
        v[m - 2] = "1"
        v[m - 1] = "1"
        u, v = "".join(u), "".join(v)
        same = windows(u, m) == windows(v, m)
        differ = u[-1] != v[-1]
        ok &= same and differ
        print(f"    m={m:2d}  labels agree: {same}   terminal digits {u[-1]} vs {v[-1]}: "
              f"{'differ' if differ else 'SAME'}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


if __name__ == "__main__":
    print("Independent check of the fibonacci_folding sharp thresholds\n")
    c = control_two_letter() and control_bijection()
    if not c:
        print("CONTROLS FAILED - the fold was implemented wrongly. Stopping.")
        sys.exit(1)
    r = [sharp_block_separation(), paper_witness(),
         causal_decoder(), optimality_witness()]
    print("SUMMARY", {"block separation sharp": r[0], "sharpness witness": r[1],
                      "decoder memory 2": r[2], "optimality witness": r[3]})
    sys.exit(0 if all(r) else 1)
