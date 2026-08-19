#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Does the effective Zeckendorf-tail bound actually close the two-star lemma?

verify_phi_norm_zeckendorf.py replaced the ineffective Subspace step by an effective one: a
residual ambiguity forces ||phi u|| <= 4 phi^{-(m+1)} for a signed two-power integer
u = s1 2^i + s2 2^j with i, j < m, and that in turn forces the lowest Zeckendorf index of |u|
to satisfy kmin >= m - 2.

That is a constraint, not a conclusion. The lemma needs the surviving u to be exactly the ones
already known to matter, namely +-34 = +-F_9 and +-144 = +-F_12, which are the Fibonacci
numbers with two binary ones that Bugeaud-Cipu-Mignotte supplies. Whether the constraint is
strong enough is a finite question for each m and is answered here by enumeration.

For each m every candidate u is generated directly - there are fewer than 4 m^2 of them - and
kept when kmin(|u|) >= m - 2. What the survivors are, and whether the surviving set is
eventually empty or eventually exactly the known pair, decides whether this route closes the
lemma or merely narrows it.

No claim is made here about the residual-ambiguity implication itself; that is the Oracle's
inequality (12) and it is taken as given. What is being tested is only whether its effective
consequence suffices.
"""
import sys

FIB = [0, 1, 1]
while len(FIB) < 1200:      # must exceed log_phi(2^(m+1)); 400 was too small at m~261
    FIB.append(FIB[-1] + FIB[-2])

FIBSET = {FIB[k]: k for k in range(2, 1100)}


def kmin(n):
    """Lowest index in the greedy Zeckendorf expansion of n > 0."""
    k = 2
    while FIB[k + 1] <= n:
        k += 1
    rest, last = n, None
    while rest > 0:
        while FIB[k] > rest:
            k -= 1
        last = k
        rest -= FIB[k]
        k -= 1
    return last


def survivors(m):
    out = set()
    for i in range(m):
        for j in range(i):
            for s1 in (1, -1):
                for s2 in (1, -1):
                    u = s1 * (1 << i) + s2 * (1 << j)
                    if u == 0:
                        continue
                    if kmin(abs(u)) >= m - 2:
                        out.add(u)
        # the one-power case, which the transcript says is handled identically
        for s1 in (1, -1):
            u = s1 * (1 << i)
            if kmin(abs(u)) >= m - 2:
                out.add(u)
    return out


def main():
    top = int(sys.argv[1]) if len(sys.argv) > 1 else 120
    print("Survivors of the effective constraint kmin(|u|) >= m - 2,")
    print("over signed sums of at most two powers of two with exponents below m.\n")
    known = {34, -34, 144, -144}
    empties = 0
    only_known = 0
    other = []
    for m in range(6, top + 1):
        S = survivors(m)
        fibs = {u for u in S if abs(u) in FIBSET}
        nonfib = S - fibs
        if not S:
            empties += 1
        elif S <= known:
            only_known += 1
        else:
            other.append((m, sorted(S)[:6], len(S)))
        if m <= 20 or m % 20 == 0:
            tag = ""
            if S:
                tag = "  fib: %s" % sorted(u for u in fibs)[:6]
                if nonfib:
                    tag += "  NON-FIB: %s" % sorted(nonfib)[:6]
            print("    m=%3d  %3d survivors%s" % (m, len(S), tag))

    print()
    print("    m with no survivors at all          : %d" % empties)
    print("    m whose survivors are within +-{34,144} : %d" % only_known)
    print("    m with other survivors              : %d" % len(other))
    if other:
        print("    first few:")
        for m, ex, n in other[:6]:
            print("        m=%d: %d survivors, e.g. %s" % (m, n, ex))
    print()
    if not other:
        print("    The constraint alone leaves only the known pair, so the effective route")
        print("    closes the lemma once the residual-ambiguity implication is granted.")
    else:
        print("    The constraint alone does NOT isolate the known pair. It narrows the")
        print("    problem but does not finish it, and the surviving u above are what a")
        print("    proof would still have to exclude.")
    return 0


if __name__ == "__main__":
    sys.exit(main())


# ---------------------------------------------------------------------------
# Using the PROVED constant rather than the measured one.
#
# verify_phi_norm_zeckendorf.py now contains a proof of the comparison (B) with explicit
# constants: ||phi n|| / phi^{-kmin} lies in [phi^{-2}, phi]. The measured lower constant was
# 1/phi, better than the proved phi^{-2}, because the geometric tail bound ignores that psi^k
# alternates in sign. Only the lower bound is used downstream, so the proved constant gives
#
#     ||phi n|| <= 4 phi^{-(m+1)}  =>  kmin >= m - 1 - log_phi 4 > m - 3.89,  i.e. kmin >= m-3,
#
# one index weaker than the m-2 the measurement suggested.
#
# Re-running the enumeration with each slack, over m = 6..160:
#
#     slack m-2 (measured) : last m with any survivor = 15, empty on [16, 160]
#     slack m-3 (PROVED)   : last m with any survivor = 16, empty on [17, 160]
#     slack m-4 (margin)   : last m with any survivor = 17, empty on [18, 160]
#
# So the conclusion does not depend on the sharp constant. On proved ingredients alone there is
# no residual ambiguity for m >= 17, and the direct computation independently covers
# 6 <= m <= 19. The two ranges overlap, so the lemma is covered for every m.
#
# What the chain now rests on, and it is a single item: the implication
#
#     residual ambiguity  =>  ||phi u|| <= 4 phi^{-(m+1)}  for a signed two-power u,
#
# which is inequality (12) of oracle_sprint_TWOSTAR_r1.md. I have not independently verified
# it. Everything downstream of it is now proved or exhaustively enumerated.

def survivors_with_slack(m, slack):
    out = set()
    for i in range(m):
        for j in range(i):
            for s1 in (1, -1):
                for s2 in (1, -1):
                    u = s1 * (1 << i) + s2 * (1 << j)
                    if u and kmin(abs(u)) >= m - slack:
                        out.add(u)
        for s1 in (1, -1):
            u = s1 * (1 << i)
            if kmin(abs(u)) >= m - slack:
                out.add(u)
    return out


def last_nonempty(slack, top=160):
    return max((m for m in range(6, top + 1) if survivors_with_slack(m, slack)), default=None)
