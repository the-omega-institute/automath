#!/usr/bin/env python3
"""
Exact algebra certificates for the manuscript.

Run from the paper root with
    python certificates/verify_exact_certificates.py

The script uses SymPy over exact rational/algebraic domains.  It is deliberately
small: each assertion corresponds to a determinant/resultant, pseudo-remainder,
Sturm-wall, or endpoint-amplitude identity printed in the paper.
"""

from __future__ import annotations

import sympy as sp


def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)


def assert_zero(name: str, expr) -> None:
    simplified = sp.factor(sp.together(expr))
    if simplified != 0:
        raise AssertionError(f"{name} failed: {simplified}")


x, y, lam, t, s, u = sp.symbols("x y lambda t s u")
rt2 = sp.sqrt(2)

Pi_lam = lam**4 - lam**3 - (2*y + 1)*lam**2 + lam + y*(y + 1)
Pi_x = x**4 - x**3 - (2*y + 1)*x**2 + x + y*(y + 1)
c = 256*y**3 + 411*y**2 + 165*y + 32

# Discriminant/resultant and endpoint substitutions.
assert_zero(
    "Disc_lambda Pi",
    sp.resultant(Pi_lam, sp.diff(Pi_lam, lam), lam) + y*(y - 1)*c,
)
assert_zero("Pi(-1,y)", Pi_lam.subs(lam, -1) - y*(y - 1))
assert_zero("Pi(0,y)", Pi_lam.subs(lam, 0) - y*(y + 1))
assert_zero("Pi(1,y)", Pi_lam.subs(lam, 1) - y*(y - 1))

# Cubic branch elimination.
p = 16*lam**3 - 9*lam**2 + 1
q = 4*y*lam - (4*lam**3 - 3*lam**2 - 2*lam + 1)
assert_zero("cubic branch resultant", sp.resultant(p, q, lam) + 64*c)

# Opposite-modulus collision certificate.
Pi_minus_x = Pi_x.subs(x, -x)
assert_zero("Pi(-x,y)-Pi(x,y)", Pi_minus_x - Pi_x - 2*x*(x**2 - 1))
assert_zero(
    "opposite-modulus resultant",
    sp.resultant(Pi_x, Pi_minus_x, x) - 16*y**3*(y - 1)**2*(y + 1),
)

# Numerator-denominator resultant and exceptional cancellations.
N = 1 + y*t + (y**2 - y - 1)*t**2 + (y**3 - 2*y)*t**3
D = 1 - t - (2*y + 1)*t**2 + t**3 + y*(y + 1)*t**4
assert_zero("Res_t(N,D)", sp.resultant(N, D, t) - y**3*(y - 1)**3*(y + 1)**6)
assert_zero("gcd at y=1", sp.gcd(sp.Poly(N.subs(y, 1), t), sp.Poly(D.subs(y, 1), t)).as_expr() - (t - 1)*(t + 1)**2)
assert_zero("gcd at y=0", sp.gcd(sp.Poly(N.subs(y, 0), t), sp.Poly(D.subs(y, 0), t)).as_expr() - (t - 1)*(t + 1))
assert_zero("gcd at y=-1", sp.gcd(sp.Poly(N.subs(y, -1), t), sp.Poly(D.subs(y, -1), t)).as_expr() - (t**3 + t**2 - t + 1))

# Positive-axis Sturm pseudo-remainder identities from Appendix B.
S0 = Pi_lam
S1 = sp.diff(Pi_lam, lam)
A2 = (16*y + 11)*lam**2 + (4*y - 10)*lam - 16*y**2 - 16*y - 1
A3 = 4*lam*y**2 - 68*lam*y - 8*lam - 64*y**3 - 41*y**2 + 25*y + 8

prem01 = sp.prem(S0, S1, lam)
prem12 = sp.prem(S1, A2, lam)
prem23 = sp.prem(A2, A3, lam)
assert_zero("prem(S0,S1)", prem01 + A2)
assert_zero("prem(S1,16S2)", prem12 - 16*A3)
assert_zero("prem(16S2,A3)", prem23 - y*(y - 1)*(16*y + 11)**2*c)
assert_zero(
    "Sturm denominator wall not discriminant wall",
    sp.resultant(-y*(y - 1)*c, y**2 - 17*y - 2, y) - 907937424,
)

# Endpoint branch and amplitude constants at y=s^2.
N_s = N.subs(y, s**2)
D_s = D.subs(y, s**2)
lambda_plus = 1 + s/rt2 + sp.Rational(5, 8)*s**2 - sp.Rational(43, 64)*s**3/rt2
lambda_minus = lambda_plus.subs(s, -s)
Pi_s = Pi_lam.subs({lam: lambda_plus, y: s**2})
check("lambda_plus root expansion", sp.series(Pi_s, s, 0, 5).removeO().expand() == 0)


def trunc(expr, order: int):
    return sp.series(expr, s, 0, order).removeO().expand()


def amplitude(lambda_branch):
    alpha = 1 / lambda_branch
    return -lambda_branch * N_s.subs(t, alpha) / sp.diff(D_s, t).subs(t, alpha)

C_plus = amplitude(lambda_plus)
C_minus = amplitude(lambda_minus)
assert_zero("C_+(s)", trunc(C_plus, 3) - (sp.Rational(1, 2) - 3*rt2*s/16 + sp.Rational(7, 16)*s**2))
assert_zero("C_-(s)", trunc(C_minus, 3) - (sp.Rational(1, 2) + 3*rt2*s/16 + sp.Rational(7, 16)*s**2))
assert_zero(
    "log lambda_+",
    trunc(sp.log(lambda_plus), 4)
    - (s/rt2 + sp.Rational(3, 8)*s**2 - sp.Rational(217, 192)*s**3/rt2),
)
assert_zero(
    "log lambda_-",
    trunc(sp.log(lambda_minus), 4)
    - (-s/rt2 + sp.Rational(3, 8)*s**2 + sp.Rational(217, 192)*s**3/rt2),
)

# Fixed-window cosine constants produced by the two-branch expansion.
m = sp.symbols("m", positive=True)
phase = u/rt2
first_order = (
    sp.Rational(1, 2)*sp.exp(sp.I*phase)*(1 - sp.I*3*rt2*u/(8*m))
    + sp.Rational(1, 2)*sp.exp(-sp.I*phase)*(1 + sp.I*3*rt2*u/(8*m))
)
expected = sp.cos(phase) + 3*u/(4*rt2*m)*sp.sin(phase)
assert_zero("cosine first-order coefficient", sp.expand(first_order.rewrite(sp.sin) - expected))

print("all exact certificates verified")
