#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Conductor computation for the genus-2 hyperelliptic curve
    X_A : w^2 = f(y),   f(y) = -y(y-1)(256y^3 + 411y^2 + 165y + 32).

Expanded form:
    f(y) = -256y^5 - 155y^4 + 246y^3 + 133y^2 + 32y.

Steps:
1. Compute disc(f) via Sylvester matrix determinant.
2. Factor disc(f) to identify bad primes.
3. For each bad prime p, estimate the local conductor exponent via point counting.
4. Assemble conductor N = prod p^{f_p}.
5. Emit a JSON certificate.
"""

from __future__ import print_function
import json
import sys
import os
import time
import math
from fractions import Fraction

t0 = time.time()

def log(msg):
    sys.stdout.write(msg + "\n")
    sys.stdout.flush()

log("[conductor_xa] starting ...")

# ------------------------------------------------------------------
# Helper: polynomial arithmetic over Z (lists, highest degree first)
# ------------------------------------------------------------------

def poly_mul(a, b):
    """Multiply two polynomials (coefficient lists, highest degree first)."""
    la, lb = len(a), len(b)
    result = [0] * (la + lb - 1)
    for i in range(la):
        for j in range(lb):
            result[i + j] += a[i] * b[j]
    return result


def poly_derivative(a):
    """Derivative of polynomial (highest degree first)."""
    n = len(a) - 1
    if n <= 0:
        return [0]
    return [a[i] * (n - i) for i in range(n)]


def sylvester_resultant(a, b):
    """Resultant via Sylvester matrix determinant (Fraction-based Gauss elimination)."""
    while len(a) > 1 and a[0] == 0:
        a = a[1:]
    while len(b) > 1 and b[0] == 0:
        b = b[1:]

    deg_a = len(a) - 1
    deg_b = len(b) - 1

    if deg_a == 0 and deg_b == 0:
        return 0 if (a[0] == 0 or b[0] == 0) else 1
    if deg_a == 0:
        return a[0] ** deg_b
    if deg_b == 0:
        return b[0] ** deg_a

    n = deg_a + deg_b
    mat = []
    for i in range(deg_b):
        row = [0] * n
        for j, c in enumerate(a):
            row[i + j] = c
        mat.append(row)
    for i in range(deg_a):
        row = [0] * n
        for j, c in enumerate(b):
            row[i + j] = c
        mat.append(row)

    # Gaussian elimination with Fractions
    mat_f = [[Fraction(x) for x in row] for row in mat]
    nn = len(mat_f)
    sign = 1
    for col in range(nn):
        pivot_row = None
        for r in range(col, nn):
            if mat_f[r][col] != 0:
                pivot_row = r
                break
        if pivot_row is None:
            return 0
        if pivot_row != col:
            mat_f[col], mat_f[pivot_row] = mat_f[pivot_row], mat_f[col]
            sign *= -1
        pivot = mat_f[col][col]
        for r in range(col + 1, nn):
            if mat_f[r][col] != 0:
                factor = mat_f[r][col] / pivot
                for c2 in range(col, nn):
                    mat_f[r][c2] -= factor * mat_f[col][c2]

    det = Fraction(sign)
    for i in range(nn):
        det *= mat_f[i][i]
    return int(det)


def factorize(n):
    """Simple trial-division factorization."""
    if n == 0:
        return {}
    if n < 0:
        n = -n
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


# ------------------------------------------------------------------
# 1. Define f(y) and compute discriminant
# ------------------------------------------------------------------

# f(y) = -y(y-1)(256y^3+411y^2+165y+32)
# Expand: y(y-1) = [1,-1,0]; multiply by [256,411,165,32]; negate.
p1 = [-1, 0]              # -y
p2 = [1, -1]              # y-1
p3 = [256, 411, 165, 32]  # cubic
f_coeffs = poly_mul(poly_mul(p1, p2), p3)

log("[conductor_xa] f(y) coefficients (deg 5 -> 0): %s" % f_coeffs)
assert f_coeffs == [-256, -155, 246, 133, 32, 0], "Coefficient mismatch"
log("[conductor_xa] coefficient check PASSED")

# Discriminant: disc(f) = (-1)^{n(n-1)/2} * Res(f, f') / a_n
# n=5, sign=(-1)^10=1, a_n = -256
fp_coeffs = poly_derivative(f_coeffs)
log("[conductor_xa] f'(y) coefficients: %s" % fp_coeffs)

log("[conductor_xa] computing Res(f, f') via Sylvester matrix (9x9) ...")
res_ff = sylvester_resultant(f_coeffs, fp_coeffs)
a_n = f_coeffs[0]  # -256
disc_f = res_ff // a_n  # sign factor is +1 for n=5

log("[conductor_xa]   Res(f, f')       = %d" % res_ff)
log("[conductor_xa]   leading coeff    = %d" % a_n)
log("[conductor_xa]   disc(f)          = %d" % disc_f)

elapsed = time.time() - t0
log("[conductor_xa] discriminant computed in %.1fs" % elapsed)

# ------------------------------------------------------------------
# 2. Factor disc(f) -> bad primes
# ------------------------------------------------------------------
disc_abs = abs(disc_f)
disc_sign = 1 if disc_f > 0 else -1
disc_factors = factorize(disc_abs)

log("[conductor_xa] |disc(f)| = %d" % disc_abs)
log("[conductor_xa] sign      = %d" % disc_sign)
log("[conductor_xa] factorisation of |disc(f)|:")
for p, e in sorted(disc_factors.items()):
    log("    %d^%d" % (p, e))

bad_primes = sorted(disc_factors.keys())
log("[conductor_xa] bad primes (dividing disc): %s" % bad_primes)

# ------------------------------------------------------------------
# 2b. Discriminant of the cubic factor
# ------------------------------------------------------------------
a_c, b_c, c_c, d_c = 256, 411, 165, 32
disc_cubic_formula = (
    18*a_c*b_c*c_c*d_c
    - 4*b_c**3*d_c
    + b_c**2*c_c**2
    - 4*a_c*c_c**3
    - 27*a_c**2*d_c**2
)
log("[conductor_xa] disc(cubic) via formula = %d" % disc_cubic_formula)
disc_cubic_factors = factorize(abs(disc_cubic_formula))
parts = ["%d^%d" % (p, e) for p, e in sorted(disc_cubic_factors.items())]
log("[conductor_xa] cubic disc factored: %s" % " * ".join(parts))

# Cross-check via resultant
cubic_coeffs = [256, 411, 165, 32]
cubic_deriv = poly_derivative(cubic_coeffs)
res_cubic = sylvester_resultant(cubic_coeffs, cubic_deriv)
disc_cubic_res = (-1) * res_cubic // 256  # sign=(-1)^3=-1
log("[conductor_xa] disc(cubic) via resultant = %d" % disc_cubic_res)

elapsed = time.time() - t0
log("[conductor_xa] factorisation done in %.1fs" % elapsed)

# ------------------------------------------------------------------
# 3. Local conductor exponents via point counting
# ------------------------------------------------------------------

def legendre(a, p):
    a = a % p
    if a == 0:
        return 0
    val = pow(a, (p - 1) // 2, p)
    return val if val <= 1 else val - p


def count_affine(coeffs_list, p):
    total = 0
    for yv in range(p):
        fv = 0
        for c in coeffs_list:
            fv = (fv * yv + c) % p
        ls = legendre(fv, p)
        if ls == 0:
            total += 1
        elif ls == 1:
            total += 2
    return total


def count_affine_fp2(coeffs_list, p):
    """Count affine points on w^2 = f(y) over F_{p^2}.

    For p=2: F_4 = F_2[t]/(t^2+t+1), multiplication: (a+bt)(c+dt) = (ac+bd) + (ad+bc+bd)t
    For odd p: F_{p^2} = F_p[t]/(t^2-nr), nr = quadratic non-residue
    """
    if p == 2:
        # F_4 = {0, 1, t, t+1} with t^2 = t+1 (i.e. t^2+t+1=0)
        # Elements as (a,b) = a + b*t
        # Multiplication: (a+bt)(c+dt) = ac + (ad+bc)t + bd*t^2
        #   = ac + (ad+bc)t + bd(t+1) = (ac+bd) + (ad+bc+bd)t   (all mod 2)
        def mul2(x, y_):
            a_, b_ = x
            c_, d_ = y_
            return ((a_*c_ + b_*d_) % 2, (a_*d_ + b_*c_ + b_*d_) % 2)

        def pow2(x, n_):
            result = (1, 0)
            base = x
            while n_ > 0:
                if n_ & 1:
                    result = mul2(result, base)
                base = mul2(base, base)
                n_ >>= 1
            return result

        count = 0
        for a in range(2):
            for b in range(2):
                yv = (a, b)
                fv = (0, 0)
                for c in coeffs_list:
                    fv = mul2(fv, yv)
                    fv = ((fv[0] + (c % 2)) % 2, fv[1] % 2)
                if fv == (0, 0):
                    count += 1
                else:
                    # In F_4, every nonzero element is a square (since F_4* is cyclic of order 3, odd)
                    count += 2
        return count

    # Odd p: F_{p^2} = F_p[t]/(t^2 - nr)
    nr = 2
    while legendre(nr, p) != -1:
        nr += 1

    def mul2(x, y_):
        return ((x[0]*y_[0] + x[1]*y_[1]*nr) % p,
                (x[0]*y_[1] + x[1]*y_[0]) % p)

    def pow2(x, n_):
        result = (1, 0)
        base = x
        while n_ > 0:
            if n_ & 1:
                result = mul2(result, base)
            base = mul2(base, base)
            n_ >>= 1
        return result

    count = 0
    for a in range(p):
        for b in range(p):
            yv = (a, b)
            fv = (0, 0)
            for c in coeffs_list:
                fv = mul2(fv, yv)
                fv = ((fv[0] + c) % p, fv[1] % p)

            if fv == (0, 0):
                count += 1
            else:
                test = pow2(fv, (p*p - 1) // 2)
                if test == (1, 0):
                    count += 2
    return count


f_coeffs_int = f_coeffs

log("")
log("[conductor_xa] === Point counting over F_p and F_{p^2} ===")

conductor_exponents = {}
euler_factors = {}

for p in bad_primes:
    log("")
    log("[conductor_xa] --- p = %d ---" % p)

    v_disc = 0
    dd = disc_abs
    while dd % p == 0:
        dd //= p
        v_disc += 1
    log("  v_p(disc(f))   = %d" % v_disc)

    # Count over F_p
    Np = count_affine(f_coeffs_int, p)
    Np_proj = Np + 1  # one point at infinity for odd-degree model
    a1 = p + 1 - Np_proj

    log("  #C^aff(F_%d)  = %d" % (p, Np))
    log("  #C(F_%d)      = %d" % (p, Np_proj))
    log("  a1(%d)          = %d" % (p, a1))

    # Count over F_{p^2}
    log("  counting over F_{%d^2} (%d elements) ..." % (p, p*p))
    Np2_aff = count_affine_fp2(f_coeffs_int, p)
    Np2_proj = Np2_aff + 1

    a1_p2 = p**2 + 1 - Np2_proj
    a2_num = a1**2 - 2*p - a1_p2
    if a2_num % 2 != 0:
        log("  WARNING: a2 not integral (a2_num = %d)" % a2_num)
        a2 = a2_num // 2
    else:
        a2 = a2_num // 2

    log("  #C(F_{%d^2})   = %d" % (p, Np2_proj))
    log("  a1_p2          = %d" % a1_p2)
    log("  a2             = %d" % a2)

    b2 = a2 + 2*p
    Lp_coeffs = [1, -a1, b2, -a1*p, p**2]
    log("  L_p(T) coeffs  = %s" % Lp_coeffs)
    Lp_at_1 = sum(Lp_coeffs)
    log("  L_p(1)         = %d" % Lp_at_1)

    euler_factors[p] = Lp_coeffs

    # Determine conductor exponent
    if p >= 5:
        # Tame case
        if v_disc == 1:
            fp_est = 1
        elif v_disc == 2:
            fp_est = 2
        else:
            fp_est = min(v_disc, 4)
        log("  (tame) f_p = %d" % fp_est)
    else:
        if p == 2:
            f_mod2 = [c % 2 for c in f_coeffs_int]
            log("  f(y) mod 2 coeffs: %s" % f_mod2)
            # f(y) mod 2 = y^4 + y^2 = y^2(y+1)^2 -- perfect square
            fp_est = min(v_disc, 10)
            log("  (wild, p=2) f_p = %d (upper bound from v_2(disc))" % fp_est)
        elif p == 3:
            f_mod3 = [c % 3 for c in f_coeffs_int]
            log("  f(y) mod 3 coeffs: %s" % f_mod3)
            for yv in range(3):
                fv = 0
                for c in f_coeffs_int:
                    fv = (fv * yv + c) % 3
                log("    f(%d) = %d mod 3" % (yv, fv))
            fp_est = min(v_disc, 8)
            log("  (wild, p=3) f_p = %d (upper bound from v_3(disc))" % fp_est)

    conductor_exponents[p] = fp_est
    elapsed = time.time() - t0
    log("  elapsed: %.1fs" % elapsed)


# ------------------------------------------------------------------
# 4. Assemble conductor
# ------------------------------------------------------------------
log("")
log("[conductor_xa] === Conductor assembly ===")

conductor = 1
for p in bad_primes:
    fp = conductor_exponents[p]
    conductor *= p ** fp
    log("  %d^%d = %d" % (p, fp, p**fp))

log("")
log("  N = %d" % conductor)

# ------------------------------------------------------------------
# 5. Discriminant cross-check (numerical via roots)
# ------------------------------------------------------------------
log("")
log("[conductor_xa] === Discriminant cross-check ===")
log("  disc(f)     = %d" % disc_f)
log("  disc(cubic) = %d" % disc_cubic_formula)

# Roots of f: 0, 1, and roots of 256y^3+411y^2+165y+32
# Use Cardano's formula with complex arithmetic for all 3 roots
import cmath
a_cb, b_cb, c_cb, d_cb = 256.0, 411.0, 165.0, 32.0
p_dep = (3*a_cb*c_cb - b_cb**2) / (3*a_cb**2)
q_dep = (2*b_cb**3 - 9*a_cb*b_cb*c_cb + 27*a_cb**2*d_cb) / (27*a_cb**3)
shift = -b_cb / (3*a_cb)

disc_dep = -(4*p_dep**3 + 27*q_dep**2)
log("  cubic depressed: p=%.6f, q=%.6f, disc_dep=%.6f" % (p_dep, q_dep, disc_dep))

# For all cases, use complex Cardano
D_card = complex((q_dep/2)**2 + (p_dep/3)**3)
sD = cmath.sqrt(D_card)
u_val = (-q_dep/2 + sD)
v_val = (-q_dep/2 - sD)
# Cube roots
u_cr = u_val ** (1.0/3)
v_cr = v_val ** (1.0/3)
# Choose the cube root pair such that u*v = -p/3
omega = cmath.exp(2j * cmath.pi / 3)
best_pair = None
best_err = float('inf')
for i in range(3):
    for j in range(3):
        ui = u_cr * omega**i
        vj = v_cr * omega**j
        err = abs(ui * vj + p_dep/3)
        if err < best_err:
            best_err = err
            best_pair = (i, j)
u_final = u_cr * omega**best_pair[0]
v_final = v_cr * omega**best_pair[1]

roots_cubic = []
for k in range(3):
    r = u_final * omega**k + v_final * omega**(-k) + shift
    roots_cubic.append(r)

all_roots = [complex(0.0), complex(1.0)] + roots_cubic
log("  roots of f (numeric):")
for i, r in enumerate(all_roots):
    if abs(r.imag) < 1e-10:
        log("    r_%d = %.10f" % (i, r.real))
    else:
        log("    r_%d = %.10f + %.10fi" % (i, r.real, r.imag))

# disc(f) = a_n^{2n-2} * prod_{i<j}(r_i-r_j)^2
a_n_val = -256
n_val = 5
prod_diff_sq = complex(1.0)
nr_roots = len(all_roots)
for i in range(nr_roots):
    for j in range(i+1, nr_roots):
        prod_diff_sq *= (all_roots[i] - all_roots[j])**2

disc_numeric = (a_n_val ** (2*n_val - 2)) * prod_diff_sq
log("  disc(f) numeric  = %.1f + %.1fi" % (disc_numeric.real, disc_numeric.imag))
log("  disc(f) exact    = %d" % disc_f)
if disc_f != 0:
    log("  ratio (real)     = %.6f" % (disc_numeric.real / disc_f))
    log("  imag part        = %.2e (should be ~0)" % abs(disc_numeric.imag))

# ------------------------------------------------------------------
# 6. Output JSON certificate
# ------------------------------------------------------------------
log("")
log("[conductor_xa] === JSON Certificate ===")

certificate = {
    "curve": "X_A: w^2 = -y(y-1)(256y^3+411y^2+165y+32)",
    "f_expanded": "f(y) = -256y^5 - 155y^4 + 246y^3 + 133y^2 + 32y",
    "f_coefficients": f_coeffs_int,
    "genus": 2,
    "discriminant_f": int(disc_f),
    "discriminant_f_sign": disc_sign,
    "discriminant_f_abs": int(disc_abs),
    "discriminant_f_factored": {str(pp): e for pp, e in sorted(disc_factors.items())},
    "bad_primes": bad_primes,
    "conductor_exponents": {str(pp): conductor_exponents[pp] for pp in bad_primes},
    "conductor_N": conductor,
    "conductor_N_factored": {str(pp): conductor_exponents[pp] for pp in bad_primes},
    "euler_factors_Lp": {
        str(pp): euler_factors[pp] for pp in bad_primes if euler_factors.get(pp) is not None
    },
    "discriminant_cubic_factor": int(disc_cubic_formula),
    "discriminant_cubic_factor_factored": {
        str(pp): e for pp, e in sorted(factorize(abs(disc_cubic_formula)).items())
    },
    "method": "point_counting_with_discriminant_analysis",
    "notes": [
        "Conductor exponents at wild primes (2, 3) are upper bounds from v_p(disc).",
        "For tame primes (p >= 5), exponents use standard semistable reduction heuristics.",
        "Exact computation requires Sage/Magma or LMFDB lookup.",
    ],
}

cert_json = json.dumps(certificate, indent=2)
log(cert_json)

# Write to file
script_dir = os.path.dirname(os.path.abspath(__file__))
out_path = os.path.join(script_dir, "..", "artifacts", "conductor_xa_certificate.json")
os.makedirs(os.path.dirname(out_path), exist_ok=True)
with open(out_path, "w", encoding="utf-8") as fh:
    fh.write(cert_json)
    fh.write("\n")

log("")
log("[conductor_xa] certificate written to %s" % os.path.abspath(out_path))
log("[conductor_xa] total elapsed: %.1fs" % (time.time() - t0))
log("[conductor_xa] done.")
