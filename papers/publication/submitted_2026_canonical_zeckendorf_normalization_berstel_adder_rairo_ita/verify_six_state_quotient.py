#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent check of the six-state quotient claims of ITA-2026-0032.

Referee 1 wrote that the only possibly original result is the minimality of the Berstel
adder, and doubted even that. The revision answers by replacing the earlier ten-state
minimality claim with two propositions:

  Prop (quotient)    output-delay normalization sends the ten-state kernel to a displayed
                     six-state transducer realizing the same complete-output function,
                     with initial state A and initial output "0"
  Prop (minimality)  the six reduced residuals are pairwise distinct, hence that quotient
                     is minimal when an initial output word is allowed

Both are checked here from the manuscript's own tables. The residual of a state q is
F_q(w) = (transition outputs from q on w) followed by the terminal word of the final
state; p(q) is the longest common prefix of F_q over all inputs; the normalized residual
is G_q with F_q(w) = p(q) G_q(w).
"""
import sys
from itertools import product

# ------------------------------------------------- the ten-state kernel (Section 5)

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
STATES = list(DELTA)


def F(q, w):
    """Residual: complete output starting from state q on input w."""
    out = []
    for ch in w:
        bit, q = DELTA[q][int(ch)]
        out.append(bit)
    return "".join(out) + OMEGA[q]


def K(w):
    return F("000", w)


def words(maxlen):
    for n in range(maxlen + 1):
        for t in product("012", repeat=n):
            yield "".join(t)


def lcp(strs):
    if not strs:
        return ""
    a, b = min(strs), max(strs)
    i = 0
    while i < len(a) and i < len(b) and a[i] == b[i]:
        i += 1
    return a[:i]


# ------------------------------------------------- the claimed quotient (Prop 6.4)

CLAIMED_P = {
    "000": "0", "001": "0", "0B2": "0", "01B": "0",
    "100": "1", "101": "1", "1B2": "1", "11B": "1",
    "002": "", "010": "",
}
CLAIMED_CLASSES = {
    "A": {"000", "100"}, "B": {"001", "101"}, "C": {"002"},
    "D": {"010"}, "E": {"0B2", "1B2"}, "F": {"01B", "11B"},
}
QUOTIENT = {
    "A": {0: ("0", "A"), 1: ("0", "B"), 2: ("", "C")},
    "B": {0: ("", "D"), 1: ("1", "A"), 2: ("1", "B")},
    "C": {0: ("01", "F"), 1: ("10", "A"), 2: ("10", "B")},
    "D": {0: ("01", "A"), 1: ("01", "B"), 2: ("10", "E")},
    "E": {0: ("0", "F"), 1: ("", "D"), 2: ("1", "A")},
    "F": {0: ("0", "B"), 1: ("", "C"), 2: ("1", "E")},
}
QOMEGA = {"A": "00", "B": "01", "C": "010", "D": "010", "E": "00", "F": "01"}
Q_INIT_STATE, Q_INIT_OUTPUT = "A", "0"


def quotient_output(w):
    q, out = Q_INIT_STATE, [Q_INIT_OUTPUT]
    for ch in w:
        o, q = QUOTIENT[q][int(ch)]
        out.append(o)
    return "".join(out) + QOMEGA[q]


# ------------------------------------------------- checks

def check_prefixes(maxlen=9):
    print("CHECK 1  the forced prefixes p(q)")
    ok = True
    for depth in (maxlen - 2, maxlen):
        got = {q: lcp([F(q, w) for w in words(depth)]) for q in STATES}
        if depth == maxlen:
            for q in STATES:
                mark = "ok" if got[q] == CLAIMED_P[q] else "MISMATCH"
                if got[q] != CLAIMED_P[q]:
                    ok = False
                print(f"    p({q:3s}) = {got[q]!r:5s} claimed {CLAIMED_P[q]!r:5s}  {mark}")
        else:
            stable = got
    # stability: the lcp must not shrink further when we look deeper
    deeper = {q: lcp([F(q, w) for w in words(maxlen)]) for q in STATES}
    if stable != deeper:
        print("    WARNING lcp not stable between depths - result is not trustworthy")
        ok = False
    else:
        print(f"    lcp stable between depth {maxlen-2} and {maxlen}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def check_classes(maxlen=9):
    print("CHECK 2  normalized residuals G_q and their classes")
    ws = list(words(maxlen))
    G = {}
    for q in STATES:
        p = CLAIMED_P[q]
        sig = []
        for w in ws:
            f = F(q, w)
            if not f.startswith(p):
                print(f"    p({q}) is not a prefix of F_{q}({w}) = {f}")
                return False
            sig.append(f[len(p):])
        G[q] = tuple(sig)
    classes = {}
    for q in STATES:
        classes.setdefault(G[q], []).append(q)
    found = sorted(sorted(v) for v in classes.values())
    claimed = sorted(sorted(v) for v in CLAIMED_CLASSES.values())
    print(f"    distinct normalized residuals: {len(found)}  (claimed 6)")
    for c in found:
        print(f"      {c}")
    ok = (len(found) == 6) and (found == claimed)
    print(f"    partition matches the claimed A-F: {found == claimed}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok, G


def check_separations(G):
    print("CHECK 3  the separating suffixes quoted in the minimality proof")
    rep = {"A": "000", "B": "001", "C": "002", "D": "010", "E": "0B2", "F": "01B"}

    def g(cls, w):
        q = rep[cls]
        return F(q, w)[len(CLAIMED_P[q]):]

    claims = [
        ("A", "E", "0", "000", "001"),
        ("B", "F", "0", "010", "001"),
        ("C", "D", "0", "0101", "0100"),
    ]
    ok = True
    for x, y, suf, ex, ey in claims:
        gx, gy = g(x, suf), g(y, suf)
        good = (gx == ex and gy == ey and gx != gy)
        if not good:
            ok = False
        print(f"    G_{x}({suf}) = {gx:6s} (paper {ex:6s})   "
              f"G_{y}({suf}) = {gy:6s} (paper {ey:6s})   "
              f"{'ok' if good else 'MISMATCH'}")
    print("    terminal outputs:", {c: F(rep[c], "")[len(CLAIMED_P[rep[c]]):] for c in rep})
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


def check_quotient_realizes(maxlen=10):
    print("CHECK 4  the six-state quotient reproduces K on every input")
    bad, total = 0, 0
    for w in words(maxlen):
        total += 1
        if quotient_output(w) != K(w):
            bad += 1
            if bad <= 3:
                print(f"    MISMATCH w={w!r} K={K(w)} quotient={quotient_output(w)}")
    print(f"    {total} words of length <= {maxlen}, {bad} mismatches")
    print(f"  -> {'PASS' if bad == 0 else 'FAIL'}\n")
    return bad == 0


def check_no_smaller(maxlen=9):
    """A five-state realization would need two of the six residuals to coincide."""
    print("CHECK 5  no two of the six reduced residuals coincide (lower bound)")
    rep = {"A": "000", "B": "001", "C": "002", "D": "010", "E": "0B2", "F": "01B"}
    ws = list(words(maxlen))
    sig = {c: tuple(F(rep[c], w)[len(CLAIMED_P[rep[c]]):] for w in ws) for c in rep}
    ok = True
    names = sorted(rep)
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            if sig[names[i]] == sig[names[j]]:
                print(f"    COLLISION {names[i]} == {names[j]}")
                ok = False
    print(f"    all {len(names)*(len(names)-1)//2} pairs distinct: {ok}")
    print(f"  -> {'PASS' if ok else 'FAIL'}\n")
    return ok


if __name__ == "__main__":
    print("Independent check of the ITA-2026-0032 six-state quotient\n")
    r1 = check_prefixes()
    r2, G = check_classes()
    r3 = check_separations(G)
    r4 = check_quotient_realizes()
    r5 = check_no_smaller()
    print("SUMMARY", {"p(q)": r1, "six classes": r2, "separations": r3,
                      "quotient realizes K": r4, "pairwise distinct": r5})
    sys.exit(0 if all([r1, r2, r3, r4, r5]) else 1)
