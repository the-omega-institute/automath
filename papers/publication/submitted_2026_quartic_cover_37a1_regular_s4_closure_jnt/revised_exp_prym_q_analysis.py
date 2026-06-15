#!/usr/bin/env python
"""
Analysis of Q = Prym(Y/E_res) where:
  - Y = X/C_4 is a genus-4 curve
  - E_res is the resolvent elliptic curve (Cremona 1147a1)
  - Y -> E_res is a degree-2 cover branched at 6 points
  - Q has dimension 3, so Jac(Y) ~ E_res x Q

Computes:
  1. a_p(E_res) for E_res: w^2 = x^3 - 16x^2 - 64x + 1040
     Minimal model discriminant: Delta = 31^2 * 37 (conductor N = 1147 = 31 * 37)
  2. a_p(E) for E = 37a1: xi^2 + xi = lambda^3 - lambda
  3. s1(X_A), s2(X_A) for X_A: w^2 = -y(y-1)(256y^3 + 411y^2 + 165y + 32)
  4. Bad-prime classification for each curve
  5. Sato-Tate statistics for E and E_res

Outputs JSON to artifacts/export/prym_q_analysis.json
"""

import json
import math
import os
import sys
import time

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def is_prime(n):
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    d = 5
    while d * d <= n:
        if n % d == 0 or n % (d + 2) == 0:
            return False
        d += 6
    return True


def primes_up_to(bound):
    return [p for p in range(2, bound + 1) if is_prime(p)]


def legendre(a, p):
    """Legendre symbol (a/p)."""
    a = a % p
    if a == 0:
        return 0
    r = pow(a, (p - 1) // 2, p)
    return r if r <= 1 else -1


# ---------------------------------------------------------------------------
# F_{p^2} arithmetic (for s2 computation on X_A)
# ---------------------------------------------------------------------------

class Fp2:
    __slots__ = ('re', 'im', 'p', 'g')

    def __init__(self, re, im, p, g):
        self.re = re % p
        self.im = im % p
        self.p = p
        self.g = g

    def __mul__(self, other):
        p, g = self.p, self.g
        re = (self.re * other.re + self.im * other.im * g) % p
        im = (self.re * other.im + self.im * other.re) % p
        return Fp2(re, im, p, g)

    def __add__(self, other):
        return Fp2((self.re + other.re) % self.p,
                    (self.im + other.im) % self.p, self.p, self.g)

    def __sub__(self, other):
        return Fp2((self.re - other.re) % self.p,
                    (self.im - other.im) % self.p, self.p, self.g)

    def __neg__(self):
        return Fp2((-self.re) % self.p, (-self.im) % self.p, self.p, self.g)

    def is_zero(self):
        return self.re == 0 and self.im == 0

    def pow(self, n):
        p, g = self.p, self.g
        result = Fp2(1, 0, p, g)
        base = Fp2(self.re, self.im, p, g)
        e = n
        while e > 0:
            if e & 1:
                result = result * base
            base = base * base
            e >>= 1
        return result

    def is_square(self):
        if self.is_zero():
            return True
        exp = (self.p * self.p - 1) // 2
        r = self.pow(exp)
        return r.re == 1 and r.im == 0

    @staticmethod
    def from_int(n, p, g):
        return Fp2(n % p, 0, p, g)


def find_non_residue(p):
    for g in range(2, p):
        if legendre(g, p) == -1:
            return g
    return None


# ---------------------------------------------------------------------------
# Curve definitions and point counting
# ---------------------------------------------------------------------------

def f_E(lam, p):
    """Discriminant of xi^2 + xi - (lam^3 - lam) = 0.
    disc = 1 + 4*(lam^3 - lam) = 4*lam^3 - 4*lam + 1."""
    return (4 * pow(lam, 3, p) - 4 * lam + 1) % p


def f_Eres(x, p):
    """E_res: w^2 = x^3 - 16x^2 - 64x + 1040 mod p."""
    return (pow(x, 3, p) - 16 * pow(x, 2, p) - 64 * x + 1040) % p


def f_XA(y, p):
    """f(y) = -y(y-1)(256y^3 + 411y^2 + 165y + 32) mod p."""
    c = (256 * pow(y, 3, p) + 411 * pow(y, 2, p) + 165 * y + 32) % p
    return ((-y % p) * ((y - 1) % p) % p * c) % p


def count_E_Fp(p):
    """Count #E(F_p) for E: xi^2 + xi = lam^3 - lam."""
    if p == 2:
        count = 1
        for lam in range(2):
            for xi in range(2):
                if (xi * xi + xi - lam * lam * lam + lam) % 2 == 0:
                    count += 1
        return count
    count = 1  # point at infinity
    for lam in range(p):
        disc = f_E(lam, p)
        leg = legendre(disc, p)
        if leg == 0:
            count += 1
        elif leg == 1:
            count += 2
    return count


def count_Eres_Fp(p):
    """Count #E_res(F_p) for w^2 = x^3 - 16x^2 - 64x + 1040."""
    count = 1  # point at infinity
    for x in range(p):
        val = f_Eres(x, p)
        leg = legendre(val, p)
        if leg == 0:
            count += 1
        elif leg == 1:
            count += 2
    return count


def count_XA_Fp(p):
    """Count #X_A(F_p) for w^2 = -y(y-1)(256y^3 + 411y^2 + 165y + 32)."""
    count = 1  # point at infinity (odd-degree model, genus 2)
    for y in range(p):
        val = f_XA(y, p)
        leg = legendre(val, p)
        if leg == 0:
            count += 1
        elif leg == 1:
            count += 2
    return count


def count_XA_Fp2(p):
    """Count #X_A(F_{p^2})."""
    g = find_non_residue(p)
    count = 1  # point at infinity
    for a in range(p):
        for b in range(p):
            y = Fp2(a, b, p, g)
            one = Fp2(1, 0, p, g)
            c256 = Fp2(256 % p, 0, p, g)
            c411 = Fp2(411 % p, 0, p, g)
            c165 = Fp2(165 % p, 0, p, g)
            c32 = Fp2(32 % p, 0, p, g)

            y2 = y * y
            y3 = y2 * y

            cy = c256 * y3 + c411 * y2 + c165 * y + c32
            ym1 = y - one
            fval = -(y * ym1 * cy)

            if fval.is_zero():
                count += 1
            elif fval.is_square():
                count += 2
    return count


# ---------------------------------------------------------------------------
# Integer factorization (small)
# ---------------------------------------------------------------------------

def factor(n):
    if n == 0:
        return {0: 1}
    factors = {}
    if n < 0:
        factors[-1] = 1
        n = -n
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


# ---------------------------------------------------------------------------
# Sato-Tate angle
# ---------------------------------------------------------------------------

def sato_tate_angle(ap, p):
    """Compute theta in [0, pi] such that a_p = 2*sqrt(p)*cos(theta)."""
    bound = 2.0 * math.sqrt(p)
    if bound == 0:
        return 0.0
    ratio = ap / bound
    ratio = max(-1.0, min(1.0, ratio))
    return math.acos(ratio)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    start_time = time.time()

    # Bad primes
    bad_E = {37}           # E = 37a1, conductor 37
    bad_Eres = {31, 37}    # E_res: Delta = 31^2 * 37, conductor 1147 = 31*37
    bad_XA = {2, 3, 31, 37}  # X_A: disc involves 2, 3, 31, 37

    all_bad = bad_E | bad_Eres | bad_XA

    all_primes = primes_up_to(100)
    good_primes = [p for p in all_primes if p not in all_bad]

    print("=" * 72)
    print("Prym variety Q = Prym(Y/E_res) analysis")
    print("=" * 72)
    print(f"E   = 37a1:  xi^2 + xi = lam^3 - lam       (conductor 37)")
    print(f"E_res:       w^2 = x^3 - 16x^2 - 64x + 1040 (conductor 1147 = 31*37)")
    print(f"X_A:         w^2 = -y(y-1)(256y^3+411y^2+165y+32)  (genus 2)")
    print(f"Q = Prym(Y/E_res), dim Q = 3")
    print()
    print(f"Bad primes: E={sorted(bad_E)}, E_res={sorted(bad_Eres)}, X_A={sorted(bad_XA)}")
    print(f"Good primes (all curves): {good_primes}")
    print(f"Total: {len(good_primes)} good primes up to 100")
    print()

    # -------------------------------------------------------------------
    # 1. Point counting for E, E_res, X_A over F_p
    # -------------------------------------------------------------------
    print("-" * 72)
    print("Point counts over F_p")
    print("-" * 72)

    results = {}
    last_progress = time.time()

    for idx, p in enumerate(good_primes):
        t0 = time.time()

        nE = count_E_Fp(p)
        nEres = count_Eres_Fp(p)
        nXA = count_XA_Fp(p)

        aE = p + 1 - nE
        aEres = p + 1 - nEres
        s1_XA = p + 1 - nXA

        # Sato-Tate angles
        theta_E = sato_tate_angle(aE, p)
        theta_Eres = sato_tate_angle(aEres, p)

        entry = {
            "p": p,
            "nE": nE, "aE": aE, "theta_E": round(theta_E, 6),
            "nEres": nEres, "aEres": aEres, "theta_Eres": round(theta_Eres, 6),
            "nXA": nXA, "s1_XA": s1_XA,
        }

        # s1(X_A) should equal a_p(E) + a_p(E_res) if Jac(X_A) ~ E x E_res
        entry["s1_check"] = (s1_XA == aE + aEres)

        # F_{p^2} count for X_A (only feasible for small p)
        if p <= 53:
            nXA2 = count_XA_Fp2(p)
            s2_XA = (s1_XA * s1_XA + nXA2 - p * p - 1) // 2
            entry["nXA_Fp2"] = nXA2
            entry["s2_XA"] = s2_XA

            # Factorization test: L_p(T) = (1 - a*T + p*T^2)(1 - b*T + p*T^2)
            # a+b = s1, a*b = s2 - 2p
            # disc = s1^2 - 4*(s2 - 2p)
            fact_disc = s1_XA * s1_XA - 4 * (s2_XA - 2 * p)
            entry["fact_disc"] = fact_disc

            if fact_disc >= 0:
                sqrt_d = int(math.isqrt(fact_disc))
                if sqrt_d * sqrt_d != fact_disc:
                    sqrt_d_check = sqrt_d + 1
                    if sqrt_d_check * sqrt_d_check == fact_disc:
                        sqrt_d = sqrt_d_check
                is_sq = (sqrt_d * sqrt_d == fact_disc)
            else:
                is_sq = False
                sqrt_d = None

            if is_sq and sqrt_d is not None:
                a1 = (s1_XA + sqrt_d) // 2
                a2 = (s1_XA - sqrt_d) // 2
                entry["L_splits"] = True
                entry["split_factors"] = [a1, a2]
                entry["match_E_Eres_full"] = (s2_XA == aE * aEres + 2 * p)
            else:
                entry["L_splits"] = False
                entry["match_E_Eres_full"] = False

            entry["L_poly_XA"] = [1, -s1_XA, s2_XA, -p * s1_XA, p * p]

        results[str(p)] = entry

        elapsed = time.time() - t0
        line = (f"  p={p:3d}: a_p(E)={aE:+4d}  a_p(E_res)={aEres:+4d}  "
                f"s1(X_A)={s1_XA:+4d}  s1_check={entry['s1_check']}")
        if p <= 53:
            line += f"  s2={entry.get('s2_XA','?'):>6}  L_splits={entry.get('L_splits','?')}"
        line += f"  [{elapsed:.2f}s]"
        print(line)

        now = time.time()
        if now - last_progress > 20:
            print(f"  ... progress: {idx+1}/{len(good_primes)} primes done, "
                  f"elapsed {now - start_time:.1f}s")
            last_progress = now

    # -------------------------------------------------------------------
    # 2. Additional analysis at bad primes (individual curves may be good)
    # -------------------------------------------------------------------
    print()
    print("-" * 72)
    print("Individual curve data at partially-bad primes")
    print("-" * 72)

    partial_data = {}
    for p in all_primes:
        if p in all_bad and p >= 5:
            entry = {"p": p, "bad_for": []}
            if p in bad_E:
                entry["bad_for"].append("E")
            else:
                nE = count_E_Fp(p)
                entry["aE"] = p + 1 - nE

            if p in bad_Eres:
                entry["bad_for"].append("E_res")
            else:
                nEres = count_Eres_Fp(p)
                entry["aEres"] = p + 1 - nEres

            if p in bad_XA:
                entry["bad_for"].append("X_A")
            else:
                nXA = count_XA_Fp(p)
                entry["s1_XA"] = p + 1 - nXA

            partial_data[str(p)] = entry
            print(f"  p={p}: bad for {entry['bad_for']}, "
                  + ", ".join(f"{k}={v}" for k, v in entry.items()
                              if k not in ("p", "bad_for")))

    # -------------------------------------------------------------------
    # 3. Sato-Tate distribution analysis
    # -------------------------------------------------------------------
    print()
    print("-" * 72)
    print("Sato-Tate distribution (angles theta = arccos(a_p / 2sqrt(p)))")
    print("-" * 72)

    # Bin into 6 equal intervals of [0, pi]
    n_bins = 6
    bins_E = [0] * n_bins
    bins_Eres = [0] * n_bins

    for p_str, entry in results.items():
        theta_E = entry["theta_E"]
        theta_Eres = entry["theta_Eres"]
        bin_E = min(int(theta_E / (math.pi / n_bins)), n_bins - 1)
        bin_Eres = min(int(theta_Eres / (math.pi / n_bins)), n_bins - 1)
        bins_E[bin_E] += 1
        bins_Eres[bin_Eres] += 1

    total = len(results)
    print(f"  {'Interval':>20s}  {'E count':>8s}  {'E frac':>8s}  {'E_res count':>11s}  {'E_res frac':>10s}")
    for i in range(n_bins):
        lo = i * math.pi / n_bins
        hi = (i + 1) * math.pi / n_bins
        label = f"[{lo:.2f}, {hi:.2f})"
        print(f"  {label:>20s}  {bins_E[i]:>8d}  {bins_E[i]/total:>8.3f}  "
              f"{bins_Eres[i]:>11d}  {bins_Eres[i]/total:>10.3f}")

    # -------------------------------------------------------------------
    # 4. Consistency checks
    # -------------------------------------------------------------------
    print()
    print("-" * 72)
    print("Consistency checks")
    print("-" * 72)

    # Hasse bound: |a_p| <= 2*sqrt(p)
    hasse_violations_E = []
    hasse_violations_Eres = []
    for p_str, entry in results.items():
        p = entry["p"]
        bound = 2.0 * math.sqrt(p)
        if abs(entry["aE"]) > bound:
            hasse_violations_E.append(p)
        if abs(entry["aEres"]) > bound:
            hasse_violations_Eres.append(p)
    print(f"  Hasse bound violations for E:     {hasse_violations_E if hasse_violations_E else 'None'}")
    print(f"  Hasse bound violations for E_res: {hasse_violations_Eres if hasse_violations_Eres else 'None'}")

    # s1(X_A) = a_p(E) + a_p(E_res) check
    s1_match_all = all(entry["s1_check"] for entry in results.values())
    s1_fail = [entry["p"] for entry in results.values() if not entry["s1_check"]]
    print(f"  s1(X_A) = a_p(E) + a_p(E_res) for all good primes: {s1_match_all}")
    if s1_fail:
        print(f"    Failures at: {s1_fail}")

    # Weil bound for genus 2: |s1| <= 2*2*sqrt(p)
    weil_violations = []
    for entry in results.values():
        p = entry["p"]
        if abs(entry["s1_XA"]) > 4.0 * math.sqrt(p):
            weil_violations.append(p)
    print(f"  Weil bound violations for X_A:    {weil_violations if weil_violations else 'None'}")

    # L-polynomial factorization summary
    primes_with_L = [entry["p"] for entry in results.values() if "L_splits" in entry]
    all_split = all(results[str(p)]["L_splits"] for p in primes_with_L)
    all_match_full = all(results[str(p)].get("match_E_Eres_full", False) for p in primes_with_L)
    print(f"  L_p(X_A) always splits (p <= 53): {all_split}")
    print(f"  L_p(X_A) = L_p(E)*L_p(E_res) for all p <= 53: {all_match_full}")

    # -------------------------------------------------------------------
    # 5. Discriminant data for E_res model
    # -------------------------------------------------------------------
    print()
    print("-" * 72)
    print("E_res model data")
    print("-" * 72)

    # E_res: w^2 = x^3 - 16x^2 - 64x + 1040
    # c4 = 48*16 - 16*(-64)... let's compute invariants properly
    # Short Weierstrass: y^2 = x^3 + ax + b  (after completing the square for x)
    # From w^2 = x^3 - 16x^2 - 64x + 1040, substitute x -> x + 16/3:
    # Not integer, so this is not minimal. The given model has:
    # a1=0, a2=-16, a3=0, a4=-64, a6=1040
    # b2 = 4*a2 = -64
    # b4 = 2*a4 = -128
    # b6 = 4*a6 = 4160
    # b8 = a2^2*a6 - a4^2 = 256*1040 - 4096 = 266240 - 4096 = 262144
    # Actually b8 = a1^2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3^2 - a4^2
    # = 0 + 4*(-16)*1040 - 0 + 0 - (-64)^2
    # = -66560 - 4096 = -70656
    # c4 = b2^2 - 24*b4 = 4096 + 3072 = 7168
    # c6 = -b2^3 + 36*b2*b4 - 216*b6
    # = 262144 + 36*(-64)*(-128) - 216*4160
    # = 262144 + 294912 - 898560
    # = -341504
    # Delta = -(c4^3 - c6^2)/1728
    # c4^3 = 7168^3 = 368244678656
    # Hmm let me just compute numerically

    a2, a4, a6 = -16, -64, 1040
    b2 = 4 * a2
    b4 = 2 * a4
    b6 = 4 * a6
    b8 = 4 * a2 * a6 - a4 * a4
    c4 = b2**2 - 24 * b4
    c6 = -b2**3 + 36 * b2 * b4 - 216 * b6
    delta_times_1728 = -(c4**3 - c6**2)
    # Actually Delta = (c4^3 - c6^2) / 1728... wait
    # Standard: Delta = -b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6
    delta = -b2**2 * b8 - 8 * b4**3 - 27 * b6**2 + 9 * b2 * b4 * b6

    print(f"  Model: w^2 = x^3 - 16x^2 - 64x + 1040")
    print(f"  b2={b2}, b4={b4}, b6={b6}, b8={b8}")
    print(f"  c4={c4}, c6={c6}")
    print(f"  Delta = {delta}")
    print(f"  Delta factored: {factor(delta)}")
    print(f"  j-invariant = c4^3/Delta = {c4**3}/{delta} = {c4**3 / delta:.6f}")

    # Scaling by u=2: c4' = c4/u^4 = c4/16, c6' = c6/u^6 = c6/64
    if c4 % 16 == 0 and c6 % 64 == 0:
        c4_min = c4 // 16
        c6_min = c6 // 64
        delta_min = delta // (2**12)
        print(f"  After u=2 scaling: c4'={c4_min}, c6'={c6_min}, Delta'={delta_min}")
        print(f"  Delta' factored: {factor(delta_min)}")

    # -------------------------------------------------------------------
    # 6. Summary table
    # -------------------------------------------------------------------
    print()
    print("=" * 72)
    print("SUMMARY TABLE: a_p values")
    print("=" * 72)
    print(f"  {'p':>4s}  {'a_p(E)':>7s}  {'a_p(E_res)':>10s}  {'s1(X_A)':>8s}  "
          f"{'s1=aE+aEr':>9s}  {'s2(X_A)':>8s}  {'L_splits':>9s}")
    print("  " + "-" * 68)
    for p_str in sorted(results.keys(), key=lambda x: int(x)):
        entry = results[p_str]
        p = entry["p"]
        s2_str = str(entry.get("s2_XA", "-"))
        split_str = str(entry.get("L_splits", "-"))
        print(f"  {p:4d}  {entry['aE']:+7d}  {entry['aEres']:+10d}  {entry['s1_XA']:+8d}  "
              f"{'YES' if entry['s1_check'] else 'NO':>9s}  {s2_str:>8s}  {split_str:>9s}")

    # -------------------------------------------------------------------
    # 7. Prym analysis: what we can deduce about Q
    # -------------------------------------------------------------------
    print()
    print("=" * 72)
    print("PRYM VARIETY Q ANALYSIS")
    print("=" * 72)
    print()
    print("  Jacobian decomposition (conjectural):")
    print("    Jac(X) ~ Jac(X_A) x E_res^2 x E^3 x Q^3")
    print("    Jac(Y) ~ E_res x Q    (Y = X/C_4, genus 4)")
    print()
    if s1_match_all:
        print("  Jac(X_A) ~ E x E_res: CONFIRMED for all good p <= 97")
    else:
        n_match = sum(1 for e in results.values() if e["s1_check"])
        n_total = len(results)
        print(f"  Jac(X_A) ~ E x E_res: NOT confirmed")
        print(f"    s1(X_A) = a_p(E) + a_p(E_res) holds at {n_match}/{n_total} good primes")
        if s1_fail:
            print(f"    Failures at p = {s1_fail}")
        print(f"    Jac(X_A) is likely simple or has a different decomposition")
    print()
    print("  To determine Q's L-function, one needs either:")
    print("    (a) An explicit model for Y to count #Y(F_p), giving")
    print("        b1(Q) = (p+1-#Y(F_p)) - a_p(E_res)")
    print("    (b) An explicit model for X (genus 16) to count #X(F_p), giving")
    print("        b1(Q) = [(p+1-#X(F_p)) - s1(X_A) - 2*a_p(E_res) - 3*a_p(E)] / 3")
    print()
    print("  Current status: E and E_res L-functions fully determined.")
    print("  Q's L-function requires an explicit genus-4 model for Y.")

    # -------------------------------------------------------------------
    # Save JSON output
    # -------------------------------------------------------------------
    output = {
        "description": "Prym variety Q = Prym(Y/E_res) analysis data",
        "curves": {
            "E": {
                "label": "37a1",
                "equation": "xi^2 + xi = lam^3 - lam",
                "conductor": 37,
                "bad_primes": sorted(bad_E)
            },
            "E_res": {
                "equation": "w^2 = x^3 - 16x^2 - 64x + 1040",
                "conductor": 1147,
                "conductor_factored": "31 * 37",
                "bad_primes": sorted(bad_Eres),
                "invariants": {
                    "b2": b2, "b4": b4, "b6": b6, "b8": b8,
                    "c4": c4, "c6": c6, "Delta": delta,
                    "Delta_factored": {str(k): v for k, v in factor(delta).items()}
                }
            },
            "X_A": {
                "equation": "w^2 = -y(y-1)(256y^3+411y^2+165y+32)",
                "genus": 2,
                "bad_primes": sorted(bad_XA)
            },
            "Q": {
                "description": "Prym(Y/E_res)",
                "dimension": 3,
                "note": "L-function undetermined; requires explicit genus-4 model for Y"
            }
        },
        "good_primes": good_primes,
        "point_count_data": results,
        "partial_bad_prime_data": partial_data,
        "sato_tate_bins": {
            "n_bins": n_bins,
            "bin_width_radians": round(math.pi / n_bins, 6),
            "E_counts": bins_E,
            "E_res_counts": bins_Eres
        },
        "consistency": {
            "hasse_violations_E": hasse_violations_E,
            "hasse_violations_Eres": hasse_violations_Eres,
            "s1_equals_aE_plus_aEres_all": s1_match_all,
            "s1_failures": s1_fail,
            "weil_violations_XA": weil_violations,
            "L_always_splits_p_le_53": all_split,
            "L_matches_E_times_Eres_p_le_53": all_match_full
        }
    }

    outdir = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          '..', 'artifacts', 'export')
    os.makedirs(outdir, exist_ok=True)
    outpath = os.path.join(outdir, 'prym_q_analysis.json')
    with open(outpath, 'w', encoding='utf-8') as fp:
        json.dump(output, fp, indent=2, ensure_ascii=False)

    total_time = time.time() - start_time
    print()
    print(f"Results saved to {outpath}")
    print(f"Total time: {total_time:.1f}s")


if __name__ == '__main__':
    main()
