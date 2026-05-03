#!/usr/bin/env python3
"""
Arithmetic audit of the genus-2 curve
    X_A: w^2 = -y(y-1)(256y^3 + 411y^2 + 165y + 32)

Computes:
  1. Point counts over F_p and F_{p^2} for good primes
  2. L-polynomial coefficients (s1, s2)
  3. Factorization test: does L_p(T) split into two quadratics?
  4. Comparison with a_p(E) and a_p(E_res) for the known elliptic quotients
  5. Discriminant of the defining polynomial

Outputs JSON audit file.
"""

import json, os, sys, time

# ---------- helpers ----------

def legendre(a, p):
    """Legendre symbol (a/p), returns -1, 0, or 1."""
    a = a % p
    if a == 0:
        return 0
    r = pow(a, (p - 1) // 2, p)
    return r if r <= 1 else -1


def poly_eval_mod(coeffs, x, p):
    """Evaluate polynomial with given coefficients (highest degree first) at x mod p."""
    result = 0
    for c in coeffs:
        result = (result * x + c) % p
    return result


# ---------- curve definitions ----------

def f_XA(y, p):
    """f(y) = -y(y-1)(256y^3 + 411y^2 + 165y + 32) mod p."""
    c = (256 * pow(y, 3, p) + 411 * pow(y, 2, p) + 165 * y + 32) % p
    return (-y * ((y - 1) % p) % p * c % p) % p


def f_E(lam, p):
    """For E: xi^2 + xi = lam^3 - lam, returns rhs = lam^3 - lam mod p.
    Points: count solutions to xi^2 + xi - (lam^3 - lam) = 0.
    Discriminant of quadratic: 1 + 4*(lam^3 - lam) = 4*lam^3 - 4*lam + 1."""
    return (4 * pow(lam, 3, p) - 4 * lam + 1) % p


def f_Eres(x, p):
    """E_res: w^2 = x^3 - 16x^2 - 64x + 1040 mod p."""
    return (pow(x, 3, p) - 16 * pow(x, 2, p) - 64 * x + 1040) % p


# ---------- point counting over F_p ----------

def count_hyperelliptic_Fp(f_func, p, genus):
    """Count points on y^2 = f(x) over F_p. For genus g, degree 2g+1 or 2g+2."""
    count = 1  # point at infinity for odd-degree model
    for x in range(p):
        val = f_func(x, p)
        leg = legendre(val, p)
        if leg == 0:
            count += 1
        elif leg == 1:
            count += 2
    return count


def count_E_Fp(p):
    """Count #E(F_p) for E: xi^2 + xi = lam^3 - lam.
    Equivalent to eta^2 = 4*lam^3 - 4*lam + 1 via eta = 2*xi + 1."""
    if p == 2:
        # Handle p=2 separately
        count = 1  # infinity
        for lam in range(2):
            for xi in range(2):
                if (xi * xi + xi - lam * lam * lam + lam) % 2 == 0:
                    count += 1
        return count
    count = 1  # infinity
    for lam in range(p):
        disc = f_E(lam, p)
        leg = legendre(disc, p)
        if leg == 0:
            count += 1
        elif leg == 1:
            count += 2
    return count


def count_Eres_Fp(p):
    """Count #E_res(F_p)."""
    count = 1  # infinity
    for x in range(p):
        val = f_Eres(x, p)
        leg = legendre(val, p)
        if leg == 0:
            count += 1
        elif leg == 1:
            count += 2
    return count


def count_XA_Fp(p):
    """Count #X_A(F_p)."""
    return count_hyperelliptic_Fp(f_XA, p, 2)


# ---------- F_{p^2} arithmetic ----------

class Fp2:
    """Element of F_{p^2} = F_p[t]/(t^2 - g) where g is a fixed non-residue."""

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
        """Check if element is a square in F_{p^2}."""
        if self.is_zero():
            return True
        exp = (self.p * self.p - 1) // 2
        r = self.pow(exp)
        return r.re == 1 and r.im == 0

    @staticmethod
    def from_int(n, p, g):
        return Fp2(n % p, 0, p, g)


def find_non_residue(p):
    """Find smallest non-residue mod p."""
    for g in range(2, p):
        if legendre(g, p) == -1:
            return g
    return None


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

            # c(y) = 256y^3 + 411y^2 + 165y + 32
            cy = c256 * y3 + c411 * y2 + c165 * y + c32

            # f(y) = -y * (y-1) * c(y)
            ym1 = y - one
            fval = -(y * ym1 * cy)

            if fval.is_zero():
                count += 1
            elif fval.is_square():
                count += 2

    return count


# ---------- discriminant ----------

def poly_discriminant_degree5():
    """Compute discriminant of f(y) = -256y^5 - 155y^4 + 246y^3 + 133y^2 + 32y.
    Using the factored form: f(y) = -y(y-1)(256y^3+411y^2+165y+32).

    Disc(f) = lead^{2n-2} * prod_{i<j}(r_i - r_j)^2
    where lead = -256, n = 5.

    Roots: 0, 1, beta_1, beta_2, beta_3 (roots of c(y)).
    """
    # We use the resultant formula instead:
    # Disc(f) = (-1)^{n(n-1)/2} * (1/a_n) * Res(f, f')
    # For f = f1 * f2 * ... * fk (pairwise coprime):
    # Disc(f) = prod Disc(fi) * prod_{i<j} Res(fi, fj)^2 * (leading coeff correction)

    # Actually, use the multiplicativity formula for squarefree polynomials:
    # Disc(fg) = Disc(f) * Disc(g) * Res(f,g)^2  (when f,g coprime)

    # f(y) = (-1) * y * (y-1) * c(y) where c(y) = 256y^3+411y^2+165y+32
    # As a polynomial: f(y) = -y(y-1)c(y)
    # Leading term: -256 * y^5

    # Disc(y) = 1 (degree 1)
    # Disc(y-1) = 1 (degree 1)
    # Disc(c) = -3^9 * 31^2 * 37

    disc_c = -(3**9) * (31**2) * 37

    # Res(y, y-1) = (-1)^{1*1} * resultant = value of y at root of y-1 = 1
    # Actually Res(y, y-1) = 1^0 * (0-1)^{1*1}... let me use the definition
    # Res(f,g) = a_n^{deg g} * prod g(alpha_i) where alpha_i are roots of f
    # Res(y, y-1): f=y has root 0, g=y-1, so Res = 1^1 * (0-1) = -1
    res_y_ym1 = -1

    # Res(y, c(y)): f=y has root 0, Res = 1^3 * c(0) = 32
    res_y_c = 32

    # Res(y-1, c(y)): f=y-1 has root 1, Res = 1^3 * c(1) = 256+411+165+32 = 864
    res_ym1_c = 864

    # For f(y) = -y(y-1)c(y), the discriminant involves the leading coefficient.
    # The discriminant of a product f = a * f1 * f2 * f3 (where a = -1 is a constant,
    # f1 = y, f2 = y-1, f3 = c(y)) is:
    #
    # For polynomial of degree n with leading coeff a_n:
    # Disc(f) = (-1)^{n(n-1)/2} / a_n * Res(f, f')
    #
    # But it's easier to use:
    # Disc(f1*f2*f3) = Disc(f1)*Disc(f2)*Disc(f3) * Res(f1,f2)^2 * Res(f1,f3)^2 * Res(f2,f3)^2
    # when all are monic. If not monic, need leading coefficient corrections.

    # Let g(y) = y(y-1)c(y) (positive leading coeff 256, degree 5)
    # Then f(y) = -g(y), so Disc(f) = Disc(-g) = (-1)^{2*5-2} * Disc(g) = Disc(g)
    # (since Disc(a*f) = a^{2n-2} * Disc(f) and (-1)^8 = 1)

    # g(y) = y * (y-1) * c(y), leading coeff 256, degree 5
    #
    # Using the formula for monic polynomials and then adjusting:
    # Let g_monic(y) = y * (y-1) * (y^3 + (411/256)y^2 + ...) -- messy
    #
    # Better: use Disc(g) = (-1)^{n(n-1)/2} * (1/a_n) * Res(g, g')
    # But computing Res(g, g') by hand is hard.
    #
    # Let me use the known formula directly:
    # Disc(f1*f2) = Disc(f1) * Disc(f2) * Res(f1,f2)^2
    # (for monic coprime polynomials)
    # For non-monic: Disc(a*f) = a^{2(deg f)-2} * Disc(f) if deg f >= 1
    # And Disc(f1*f2) when f1 has leading coeff a and f2 has leading coeff b:
    # This gets complicated. Let me just compute it via the expanded polynomial.

    # f(y) = -256y^5 - 155y^4 + 246y^3 + 133y^2 + 32y + 0
    # Let me verify the expansion first

    # y(y-1) = y^2 - y
    # (y^2-y)(256y^3+411y^2+165y+32)
    # = 256y^5 + 411y^4 + 165y^3 + 32y^2 - 256y^4 - 411y^3 - 165y^2 - 32y
    # = 256y^5 + 155y^4 - 246y^3 - 133y^2 - 32y
    # So f(y) = -(256y^5 + 155y^4 - 246y^3 - 133y^2 - 32y)
    # = -256y^5 - 155y^4 + 246y^3 + 133y^2 + 32y

    # Coefficients [a5, a4, a3, a2, a1, a0] = [-256, -155, 246, 133, 32, 0]
    coeffs = [-256, -155, 246, 133, 32, 0]

    # Compute Disc via Sylvester matrix / resultant
    # Disc(f) = (-1)^{n(n-1)/2} / a_n * Res(f, f')
    # f'(y) = -1280y^4 - 620y^3 + 738y^2 + 266y + 32
    f_prime_coeffs = [-1280, -620, 738, 266, 32]

    # Compute resultant via Sylvester determinant
    # This is a 9x9 determinant -- let me use a simple implementation

    n = 5  # degree of f
    m = 4  # degree of f'
    size = n + m  # = 9

    # Build Sylvester matrix
    mat = [[0] * size for _ in range(size)]

    # m rows from f (each shifted)
    for i in range(m):
        for j, c in enumerate(coeffs):
            mat[i][i + j] = c

    # n rows from f'
    for i in range(n):
        for j, c in enumerate(f_prime_coeffs):
            mat[m + i][i + j] = c

    # Compute determinant using fraction-free Gaussian elimination
    # (to stay in exact integer arithmetic)
    from fractions import Fraction
    fmat = [[Fraction(mat[i][j]) for j in range(size)] for i in range(size)]

    det = Fraction(1)
    for col in range(size):
        # Find pivot
        pivot_row = None
        for row in range(col, size):
            if fmat[row][col] != 0:
                pivot_row = row
                break
        if pivot_row is None:
            return 0
        if pivot_row != col:
            fmat[col], fmat[pivot_row] = fmat[pivot_row], fmat[col]
            det = -det

        det *= fmat[col][col]
        pivot = fmat[col][col]

        for row in range(col + 1, size):
            factor = fmat[row][col] / pivot
            for j in range(col, size):
                fmat[row][j] -= factor * fmat[col][j]

    resultant = int(det)

    # Disc(f) = (-1)^{n(n-1)/2} / a_n * Res(f, f')
    sign = (-1) ** (n * (n - 1) // 2)  # (-1)^10 = 1
    disc = sign * resultant // coeffs[0]  # integer division, a_n = -256

    return disc, resultant


# ---------- main computation ----------

def main():
    start_time = time.time()

    # Bad primes for X_A
    bad_primes = {2, 3, 31, 37}

    # Good primes to test
    test_primes = [p for p in range(5, 100) if all(p % q != 0 for q in range(2, p)) and p not in bad_primes]
    # Filter to actual primes
    def is_prime(n):
        if n < 2:
            return False
        for d in range(2, int(n**0.5) + 1):
            if n % d == 0:
                return False
        return True
    test_primes = [p for p in range(5, 100) if is_prime(p) and p not in bad_primes]

    print(f"Testing {len(test_primes)} good primes: {test_primes}")
    print()

    results = {}

    for idx, p in enumerate(test_primes):
        t0 = time.time()

        # Count points on E, E_res, X_A over F_p
        nE = count_E_Fp(p)
        nEres = count_Eres_Fp(p)
        nXA = count_XA_Fp(p)

        aE = p + 1 - nE
        aEres = p + 1 - nEres
        s1 = p + 1 - nXA  # trace of Frobenius on H^1 of X_A

        # Count points on X_A over F_{p^2} (expensive for large p)
        if p <= 53:
            nXA2 = count_XA_Fp2(p)
            s2 = (s1 * s1 + nXA2 - p * p - 1) // 2

            # Factorization discriminant: s1^2 - 4*(s2 - 2p)
            # If L_p(T) = (1-aT+pT^2)(1-bT+pT^2), then a+b=s1, ab=s2-2p
            # So a,b are roots of x^2 - s1*x + (s2-2p) = 0
            # Discriminant = s1^2 - 4(s2-2p)
            fact_disc = s1 * s1 - 4 * (s2 - 2 * p)

            # Check if it's a perfect square
            if fact_disc >= 0:
                sqrt_d = int(fact_disc ** 0.5)
                is_perfect_sq = (sqrt_d * sqrt_d == fact_disc) or ((sqrt_d + 1) * (sqrt_d + 1) == fact_disc)
                if (sqrt_d + 1) * (sqrt_d + 1) == fact_disc:
                    sqrt_d = sqrt_d + 1
            else:
                is_perfect_sq = False
                sqrt_d = None

            # If splits, recover a_p of the two elliptic factors
            if is_perfect_sq and sqrt_d is not None:
                a_factor1 = (s1 + sqrt_d) // 2
                a_factor2 = (s1 - sqrt_d) // 2
                split_info = {"splits": True, "a1": a_factor1, "a2": a_factor2}
            else:
                split_info = {"splits": False, "fact_disc": fact_disc}

            # Check if Jac(X_A) ~ E x E_res
            match_E_Eres = (s1 == aE + aEres) and (s2 == aE * aEres + 2 * p)

            results[str(p)] = {
                "nE": nE, "nEres": nEres, "nXA": nXA,
                "aE": aE, "aEres": aEres, "s1": s1,
                "nXA_Fp2": nXA2, "s2": s2,
                "fact_disc": fact_disc,
                "split_info": split_info,
                "match_E_Eres": match_E_Eres,
                "L_poly": [1, -s1, s2, -p * s1, p * p]
            }
        else:
            results[str(p)] = {
                "nE": nE, "nEres": nEres, "nXA": nXA,
                "aE": aE, "aEres": aEres, "s1": s1,
                "s1_vs_aE_plus_aEres": s1 == aE + aEres
            }

        elapsed = time.time() - t0
        print(f"  p={p:3d}: #E={nE}, a_p(E)={aE:+d}; #E_res={nEres}, a_p(E_res)={aEres:+d}; "
              f"#X_A={nXA}, s1={s1:+d}"
              + (f"; s2={results[str(p)].get('s2','?')}; fact_disc={results[str(p)].get('fact_disc','?')}"
                 + f"; split={results[str(p)].get('split_info',{}).get('splits','?')}"
                 + f"; ~ExE_res={results[str(p)].get('match_E_Eres','?')}"
                 if p <= 53 else "")
              + f"  [{elapsed:.1f}s]")

    # Compute polynomial discriminant
    print("\nComputing discriminant of f(y) = -y(y-1)(256y^3+411y^2+165y+32)...")
    disc, res = poly_discriminant_degree5()
    print(f"  Resultant Res(f, f') = {res}")
    print(f"  Disc(f) = {disc}")

    # Factor the discriminant
    def factor(n):
        if n < 0:
            factors = {-1: 1}
            n = -n
        else:
            factors = {}
        d = 2
        while d * d <= n:
            while n % d == 0:
                factors[d] = factors.get(d, 0) + 1
                n //= d
            d += 1
        if n > 1:
            factors[n] = factors.get(n, 0) + 1
        return factors

    disc_factors = factor(disc)
    print(f"  Factored: {disc_factors}")

    # Summary analysis
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)

    # Check if s1 = aE + aEres for all primes
    all_match = all(
        results[str(p)].get("match_E_Eres", results[str(p)].get("s1_vs_aE_plus_aEres", None))
        for p in test_primes
    )
    print(f"\nJac(X_A) ~ E x E_res for ALL good primes? {all_match}")

    # Check if L_p(T) always splits
    primes_with_s2 = [p for p in test_primes if p <= 53]
    always_splits = all(results[str(p)]["split_info"]["splits"] for p in primes_with_s2)
    print(f"L_p(T) always splits (p <= 53)? {always_splits}")

    if always_splits:
        print("\nSplit factors at each prime:")
        for p in primes_with_s2:
            info = results[str(p)]["split_info"]
            print(f"  p={p}: a1={info['a1']}, a2={info['a2']}, "
                  f"a_E={results[str(p)]['aE']}, a_E_res={results[str(p)]['aEres']}")

    # Check simplicity: if fact_disc < 0 for any prime, Jac is simple
    simple_evidence = [p for p in primes_with_s2 if results[str(p)]["fact_disc"] < 0]
    if simple_evidence:
        print(f"\nJac(X_A) is SIMPLE: fact_disc < 0 at primes {simple_evidence}")
    else:
        print("\nNo evidence of simplicity from factorization discriminant (all non-negative)")

    # Save results
    output = {
        "curve": "X_A: w^2 = -y(y-1)(256y^3+411y^2+165y+32)",
        "bad_primes": sorted(bad_primes),
        "polynomial_discriminant": disc,
        "discriminant_factorization": {str(k): v for k, v in disc_factors.items()},
        "point_counts": results,
        "analysis": {
            "Jac_matches_E_times_Eres": all_match,
            "L_poly_always_splits": always_splits,
            "simple_evidence_primes": simple_evidence if simple_evidence else None
        }
    }

    outdir = os.path.join(os.path.dirname(__file__), '..', 'artifacts', 'export')
    os.makedirs(outdir, exist_ok=True)
    outpath = os.path.join(outdir, 'genus2_jacobian_audit.json')
    with open(outpath, 'w') as fp:
        json.dump(output, fp, indent=2)
    print(f"\nResults saved to {outpath}")

    total = time.time() - start_time
    print(f"Total time: {total:.1f}s")


if __name__ == '__main__':
    main()
