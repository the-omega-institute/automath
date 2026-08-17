"""Exhaustive search for minimal ambiguous cores of the Zeckendorf window fold.

Ground truth for the question I put to the oracle: the published bound
"every ambiguous core has length at most r+1 = 4" is false, and I want to know
what the longest minimal core actually is, as a function of m and of the raw
block length L.

Conventions are the paper's, low-to-high: position k carries weight F_{k+1}
with F_2=1, F_3=2, F_4=3, ...;  Fold_m(w) = Zeckendorf normal form of
N(w) mod F_{m+2}, a length-m admissible word.

A pair of distinct raw blocks of the same length L is ambiguous when their
consecutive length-m windows carry identical labels.  A coordinate is passive
when deleting it from both blocks leaves two DISTINCT blocks that are still
ambiguous at level m-1.  A minimal core is an ambiguous pair with no passive
coordinate.
"""
import sys
from itertools import product

sys.stdout.reconfigure(encoding='utf-8', errors='replace')

F = [0, 1]
while len(F) < 40:
    F.append(F[-1] + F[-2])


def N(w):
    return sum(w[k] * F[k + 2] for k in range(len(w)))


def zeck(v, m):
    out = [0] * m
    for k in range(m, 0, -1):
        if F[k + 1] <= v:
            out[k - 1] = 1
            v -= F[k + 1]
    return tuple(out) if v == 0 else None


def fold(w, m):
    return zeck(N(w) % F[m + 2], m)


def labels(w, m):
    n = len(w) - m + 1
    if n < 1:
        return None
    return tuple(fold(w[i:i + m], m) for i in range(n))


def ambiguous(u, v, m):
    return u != v and labels(u, m) == labels(v, m)


def is_minimal(u, v, m):
    """no single coordinate deletion leaves a distinct ambiguous pair at level m-1"""
    if m - 1 < 1:
        return True
    for j in range(len(u)):
        u2 = u[:j] + u[j + 1:]
        v2 = v[:j] + v[j + 1:]
        if u2 != v2 and labels(u2, m - 1) == labels(v2, m - 1):
            return False
    return True


print("m   L   ambiguous pairs   minimal cores   longest minimal core at this L")
print("-" * 76)
best = {}
for m in range(2, 7):
    for L in range(m + 1, m + 8):
        if 2 ** L > 2 ** 18:
            break
        groups = {}
        for w in product((0, 1), repeat=L):
            lab = labels(w, m)
            if lab is None:
                continue
            groups.setdefault(lab, []).append(w)
        amb = 0
        mins = 0
        for lab, ws in groups.items():
            if len(ws) < 2:
                continue
            for i in range(len(ws)):
                for j in range(i + 1, len(ws)):
                    amb += 1
                    if is_minimal(ws[i], ws[j], m):
                        mins += 1
                        if L > best.get(m, (0, None))[0]:
                            best[m] = (L, (ws[i], ws[j]))
        print("%2d %3d %17d %15d   %s"
              % (m, L, amb, mins, L if mins else "-"))
    print()

print("longest minimal ambiguous core found, per m:")
for m in sorted(best):
    L, pair = best[m]
    print("  m=%d : length %d   e.g. %s vs %s"
          % (m, L, "".join(map(str, pair[0])), "".join(map(str, pair[1]))))
print()
print("published bound was r+1 = 4, independent of m.")
print("control: if the search were blind every 'ambiguous pairs' column would be 0.")

# --- extension run, tick 318 -------------------------------------------------
# The bound 2m-2 was read off m = 3..6.  Testing it on values it was not derived
# from:  m=7 gives 12 and m=8 gives 14, both equal to 2m-2, with the witness
# family continuing unchanged - a single 1 at position m+1 against the adjacent
# pair at positions m-1, m, i.e. F_{m+2} = F_{m+1} + F_m.
#
#   m=7  longest minimal core 12  witness 000000010000 vs 000001100000
#   m=8  longest minimal core 14  witness 00000000100000 vs 00000011000000
#
# Six values of m now agree.  This is evidence, not a proof: the search is
# exhaustive in L only up to the cutoff, so it rules out longer cores only
# within that range.
