#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent check of the two iteration-depth theorems of ITA-2026-0032.

After the revision conceded the qualitative results to Frougny, Sakarovitch, Berstel and
Mousavi-Schaeffer-Shallit, these two bounds carry the paper's entire novelty claim:

    Theorem (binary cleanup)      max { tau(u) : u in {0,1}^L, u trimmed }  = floor(L/2)
    Theorem (genuine additions)   max { tau(w) : w in Add_2^MSD(n) }        = ceil(n/2)

Everything below is transcribed from the manuscript: the ten-state transducer of
Section 5, Val_MSD(w) = sum d_i F_{n-i+2}, Berstel(w) = trimMSD(K(trimMSD(w))), the depth
tau(w) = min{t : Berstel^t(trimMSD(w)) = Z_MSD(w)}, the cascade depth D(u) counting
factors (10)^r 11, and the characterisation of Add_2^MSD(n) as the words with no factor
12, 21 or 22.

Nothing downstream means anything unless the transducer was transcribed correctly, so the
script refuses to report on the theorems until value preservation passes.
"""
import sys, time
from itertools import product

# ---------------------------------------------------------------- the transducer

# States written as in the paper; 'B' stands for the overbar (digit -1).
Q = ["000", "001", "002", "010", "100", "101", "0B2", "1B2", "01B", "11B"]

# delta[state][input digit] = (output bit, next state)
DELTA = {
    "000": {0: ("0", "000"), 1: ("0", "001"), 2: ("0", "002")},
    "100": {0: ("1", "000"), 1: ("1", "001"), 2: ("1", "002")},
    "001": {0: ("0", "010"), 1: ("0", "100"), 2: ("0", "101")},
    "002": {0: ("0", "11B"), 1: ("1", "000"), 2: ("1", "001")},
    "010": {0: ("0", "100"), 1: ("0", "101"), 2: ("1", "0B2")},
    "101": {0: ("1", "010"), 1: ("1", "100"), 2: ("1", "101")},
    "0B2": {0: ("0", "01B"), 1: ("0", "010"), 2: ("0", "100")},
    "1B2": {0: ("1", "01B"), 1: ("1", "010"), 2: ("1", "100")},
    "01B": {0: ("0", "001"), 1: ("0", "002"), 2: ("0", "1B2")},
    "11B": {0: ("1", "001"), 1: ("1", "002"), 2: ("1", "1B2")},
}

OMEGA = {
    "000": "000", "001": "001", "002": "010", "010": "010", "100": "100",
    "101": "101", "0B2": "000", "1B2": "100", "01B": "001", "11B": "101",
}


def K(w):
    """Complete output of the subsequential transducer, initial state 000."""
    q, out = "000", []
    for ch in w:
        bit, q = DELTA[q][int(ch)]
        out.append(bit)
    return "".join(out) + OMEGA[q]


# ---------------------------------------------------------------- values

FIB = [0, 1, 1]                      # FIB[1] = F_1 = 1, FIB[2] = F_2 = 1
while len(FIB) < 200:
    FIB.append(FIB[-1] + FIB[-2])


def val(w):
    """Val_MSD(w) = sum_{i=1..n} d_i F_{n-i+2}."""
    n = len(w)
    return sum(int(d) * FIB[n - i + 1] for i, d in enumerate(w))


def trim(w):
    s = w.lstrip("0")
    return s if s else "0"


def berstel(w):
    return trim(K(trim(w)))


def z_msd(v):
    """Greedy Zeckendorf word, MSD first, weights F_2, F_3, ... ; Z(0) = '0'."""
    if v == 0:
        return "0"
    k = 2
    while FIB[k + 1] <= v:
        k += 1
    digits = []
    for j in range(k, 1, -1):
        if FIB[j] <= v:
            digits.append("1")
            v -= FIB[j]
        else:
            digits.append("0")
    return "".join(digits)


def tau(w, cap=200):
    target = z_msd(val(w))
    cur = trim(w)
    for t in range(cap):
        if cur == target:
            return t
        cur = berstel(cur)
    return None


def cascade_depth(u):
    s = trim(u)
    best = 0
    for r in range(0, len(s) + 1):
        if ("10" * r) + "11" in s:
            best = max(best, r + 1)
    return best


# ---------------------------------------------------------------- controls

def control_value_preservation(maxlen=9):
    print("CONTROL 1  value preservation of the transducer")
    bad = 0
    total = 0
    for n in range(1, maxlen + 1):
        for tup in product("012", repeat=n):
            w = "".join(tup)
            total += 1
            if val(K(w)) != val(w):
                bad += 1
                if bad <= 3:
                    print(f"    MISMATCH w={w} val={val(w)} K(w)={K(w)} val={val(K(w))}")
        print(f"    length {n}: cumulative {total} words, {bad} mismatches", flush=True)
    print(f"  -> {total} words checked, {bad} mismatches\n")
    return bad == 0


def control_greedy_roundtrip(vmax=20000):
    print("CONTROL 2  greedy Zeckendorf word is admissible and has the right value")
    bad = 0
    for v in range(vmax):
        z = z_msd(v)
        if val(z) != v or "11" in z:
            bad += 1
            if bad <= 3:
                print(f"    MISMATCH v={v} z={z} val={val(z)}")
    print(f"  -> {vmax} values checked, {bad} mismatches\n")
    return bad == 0


# ---------------------------------------------------------------- the theorems

def theorem_binary_cleanup(maxL=20):
    print("THEOREM 1  max tau over trimmed binary words of length L  ==  floor(L/2)")
    ok = True
    t0 = time.time()
    for L in range(1, maxL + 1):
        best, arg = -1, None
        if L == 1:
            words = ["0", "1"]
        else:
            words = ["1" + "".join(t) for t in product("01", repeat=L - 1)]
        for u in words:
            d = tau(u)
            if d is None:
                print(f"    L={L}: tau did not converge on {u}")
                ok = False
                continue
            if d > best:
                best, arg = d, u
        pred = L // 2
        flag = "ok" if best == pred else "MISMATCH"
        if best != pred:
            ok = False
        print(f"    L={L:2d}  max tau = {best:2d}   floor(L/2) = {pred:2d}   {flag}"
              f"   witness {arg}", flush=True)
        if time.time() - t0 > 20:
            t0 = time.time()
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def add2_words(n):
    """Length-n words over {0,1,2} with no factor 12, 21, 22."""
    out = []
    for tup in product("012", repeat=n):
        w = "".join(tup)
        if "12" in w or "21" in w or "22" in w:
            continue
        out.append(w)
    return out


def theorem_genuine_addition(maxn=14):
    print("THEOREM 2  max tau over Add_2^MSD(n)  ==  ceil(n/2)")
    ok = True
    t0 = time.time()
    for n in range(1, maxn + 1):
        best, arg = -1, None
        for w in add2_words(n):
            d = tau(w)
            if d is None:
                print(f"    n={n}: tau did not converge on {w}")
                ok = False
                continue
            if d > best:
                best, arg = d, w
        pred = -(-n // 2)
        flag = "ok" if best == pred else "MISMATCH"
        if best != pred:
            ok = False
        print(f"    n={n:2d}  max tau = {best:2d}   ceil(n/2) = {pred:2d}   {flag}"
              f"   witness {arg}", flush=True)
        if time.time() - t0 > 20:
            t0 = time.time()
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def lemma_tau_le_cascade(maxL=16):
    print("LEMMA  tau(u) <= D(u) on binary words, and D(u) <= floor(L/2)")
    ok = True
    for L in range(1, maxL + 1):
        for t in product("01", repeat=L):
            u = "".join(t)
            d, c = tau(u), cascade_depth(u)
            if d is None or d > c or c > L // 2:
                print(f"    MISMATCH L={L} u={u} tau={d} D={c}")
                ok = False
                break
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


if __name__ == "__main__":
    print("Independent check of ITA-2026-0032 Berstel iteration depth\n")
    c1 = control_value_preservation()
    c2 = control_greedy_roundtrip()
    if not (c1 and c2):
        print("CONTROLS FAILED - the transducer or value map was transcribed wrongly.")
        print("No conclusion about the theorems can be drawn. Stopping.")
        sys.exit(1)
    r0 = lemma_tau_le_cascade()
    r1 = theorem_binary_cleanup()
    r2 = theorem_genuine_addition()
    print("SUMMARY", {"lemma tau<=D<=L/2": r0, "binary cleanup floor(L/2)": r1,
                      "genuine addition ceil(n/2)": r2})
    sys.exit(0 if (r0 and r1 and r2) else 1)


def theorem_genuine_addition_trimmed(maxn=14):
    """The revision claims the ceil(n/2) maximum is attained WITHOUT leading-zero padding."""
    print("REFINEMENT  is the Add_2 maximum attained by a TRIMMED word?")
    ok = True
    for n in range(1, maxn + 1):
        best, arg = -1, None
        for w in add2_words(n):
            if n > 1 and w[0] == "0":
                continue
            d = tau(w)
            if d is not None and d > best:
                best, arg = d, w
        pred = -(-n // 2)
        flag = "ok" if best == pred else "MISMATCH"
        if best != pred:
            ok = False
        print(f"    n={n:2d}  max tau over trimmed = {best:2d}   ceil(n/2) = {pred:2d}"
              f"   {flag}   witness {arg}", flush=True)
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok
