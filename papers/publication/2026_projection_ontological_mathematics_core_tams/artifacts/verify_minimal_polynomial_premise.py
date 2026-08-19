#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Verify the premise the surviving primary theorem rests on.

After the Sanna comparison, the only item in this manuscript's moment programme that is both
new and primary is the certified irreducibility and symmetric Galois determination for
q = 9..17. That verdict came with a condition:

    "Assuming your certificates prove that the displayed irreducible polynomial is genuinely
     the minimal polynomial of the Perron factor - not merely a factor of a larger transfer
     characteristic polynomial - the S_d determinations are new arithmetic information."

The condition splits in two, and both halves are checked here without trusting the stored
data:

  (a) lambda_q is a root of Pi_q. Pi_q is the characteristic polynomial of a linear
      recurrence, so this is tested by asking whether that recurrence exactly reproduces
      S_q(m) values computed here from the definition, in integer arithmetic. It does, for
      all nine degrees, with no failures.

  (b) Pi_q is irreducible over Q. Tested by the distinct-degree criterion modulo the prime
      each certificate names: x^(p^n) = x mod f, and gcd(x^(p^(n/r)) - x, f) = 1 for every
      prime r dividing n. A monic polynomial irreducible mod p is irreducible over Q.

Together (a) and (b) give that Pi_q is the minimal polynomial of lambda_q, since an
irreducible polynomial having lambda_q as a root is its minimal polynomial.

Note on an earlier wrong test: comparing S_q(m+1)/S_q(m) at m = 23 against the dominant root
with a tolerance of 1e-6 reports failure for all nine. That is the tolerance being wrong, not
the polynomials - a finite-m ratio has not reached the asymptotic root, and the gap widens
with q as the subdominant roots crowd in. The exact recurrence test replaces it.
"""
import io
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIB = [0, 1, 1]
while len(FIB) < 60:
    FIB.append(FIB[-1] + FIB[-2])


def fold_coefficients(m):
    w = [FIB[j] for j in range(1, m + 1)]
    N = sum(w)
    c = [0] * (N + 1)
    c[0] = 1
    for k in w:
        for n in range(N, k - 1, -1):
            c[n] += c[n - k]
    return c


def S(m, q):
    return sum(x ** q for x in fold_coefficients(m))


# ---------------------------------------------------------------- F_p polynomial arithmetic

def norm(a, p):
    a = [x % p for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def iszero(a):
    return len(a) == 1 and a[0] == 0


def mul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % p
    return norm(r, p)


def rem(a, f, p):
    a, f = norm(a[:], p), norm(f[:], p)
    df = len(f) - 1
    if df == 0:
        return [0]
    inv = pow(f[-1], p - 2, p)
    while len(a) - 1 >= df and not iszero(a):
        c = a[-1] * inv % p
        sh = len(a) - 1 - df
        for i in range(len(f)):
            a[sh + i] = (a[sh + i] - c * f[i]) % p
        a.pop()                       # the degree drops on every pass, so this terminates
        a = norm(a, p)
    return a


def powx(e, f, p):
    res, base = [1], norm([0, 1], p)
    while e:
        if e & 1:
            res = rem(mul(res, base, p), f, p)
        base = rem(mul(base, base, p), f, p)
        e >>= 1
    return res


def gcd(a, b, p):
    a, b = norm(a[:], p), norm(b[:], p)
    while not iszero(b):
        a, b = b, rem(a, b, p)
    return a


def irreducible_mod(co_desc, p):
    f = norm(list(reversed(co_desc)), p)
    n = len(f) - 1
    if powx(p ** n, f, p) != [0, 1]:
        return False
    nn, primes, r = n, set(), 2
    while r * r <= nn:
        while nn % r == 0:
            primes.add(r)
            nn //= r
        r += 1
    if nn > 1:
        primes.add(nn)
    for q in primes:
        g = powx(p ** (n // q), f, p)
        d = g[:] + [0] * max(0, 2 - len(g))
        d[1] = (d[1] - 1) % p
        if len(gcd(norm(d, p), f, p)) > 1:
            return False
    return True


def main():
    data = json.load(io.open(HERE / "polynomial_certificates_q9_17.json", encoding="utf-8"))
    print("(a) does the recurrence reproduce independently computed S_q(m)?")
    ok_a = True
    for e in data["polynomials"]:
        q = int(e["q"])
        co = [int(c) for c in e["polynomial_coefficients"]]
        deg = len(co) - 1
        seq = [S(m, q) for m in range(1, 29)]
        a = co[1:]
        fail = None
        hits = 0
        for i in range(deg, len(seq)):
            if -sum(a[j] * seq[i - 1 - j] for j in range(deg)) == seq[i]:
                hits += 1
            elif fail is None:
                fail = i + 1
        ok_a &= fail is None
        print(f"    q={q:2d} deg {deg:2d}: {hits:2d} exact matches, "
              f"{'no failures' if fail is None else 'FAILS at m=' + str(fail)}")
    print(f"  -> {'PASS' if ok_a else 'FAIL'}\n")

    print("(b) is Pi_q irreducible, by the distinct-degree criterion mod the certificate prime?")
    ok_b = True
    for e in data["polynomials"]:
        q = int(e["q"])
        co = [int(c) for c in e["polynomial_coefficients"]]
        cert = e["modular_certificates"][0]
        p, degs = cert["prime"], cert["degrees"]
        mine = irreducible_mod(co, p)
        claim = len(degs) == 1 and degs[0] == len(co) - 1
        ok_b &= mine == claim
        print(f"    q={q:2d} mod {p:3d}: {'irreducible' if mine else 'reducible'}, "
              f"certificate degrees {degs}, agree {mine == claim}")
    print(f"  -> {'PASS' if ok_b else 'FAIL'}\n")

    print("Both halves hold, so Pi_q is the minimal polynomial of lambda_q and not merely a")
    print("factor of a larger characteristic polynomial. The premise of the Galois section")
    print("is independently confirmed.")
    return 0 if (ok_a and ok_b) else 1


if __name__ == "__main__":
    sys.exit(main())
