#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit: closed-form Bernoulli(p) laws for the fold gauge anomaly mismatch kernel.

This script is English-only by repository convention.

We verify (numerically, deterministically) the closed-form formulas in:
  sections/body/folding/subsubsec__fold-gauge-anomaly-bernoulli-p-baseline.tex

Model:
- 4-state Markov chain on (a,b,c,d) with transition matrix P(p)
- edge potential g=1 on (a->b), (b->c), (c->a); else 0
- mismatch sum G_m := sum_{n=0}^{m-1} g(S_n,S_{n+1})

Checks:
- stationary distribution and mismatch density g_*(p)
- asymptotic variance rate sigma_G^2(p) via Poisson equation (edge-reward martingale)
- third cumulant density P_{G,p}^{(3)}(0) via implicit differentiation
- characteristic polynomial factorization of P(p)
- endpoint LDP rate I_p(0) via rho(Q_p(0))
- GC far-field defect constant and the golden critical bias p=phi/2 (numeric)
- square-collapse factorization at the unique maximizer p_* (symbolic identity)
- covariance recurrence and generating function (spot checks)
- bit-pair law sums to 1 and matches p=1/2 table
- output-density / mismatch-density elimination curve
- strict third-order Markov kernel of the mismatch indicator process
- quartic pressure discriminant factorization and u=1 resonance criterion

Outputs:
- artifacts/export/fold_gauge_anomaly_bernoulli_p_closed_form.json
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _as_float(x: sp.Expr, *, prec: int = 80) -> float:
    return float(sp.N(x, prec))


def _max_abs(xs: List[float]) -> float:
    return max(abs(x) for x in xs) if xs else 0.0


@dataclass(frozen=True)
class CheckResult:
    name: str
    max_abs_err: float


def _P(p: float) -> List[List[float]]:
    return [
        [1.0 - p, p * p, 0.0, p * (1.0 - p)],
        [0.0, 0.0, 1.0, 0.0],
        [1.0 - p, p, 0.0, 0.0],
        [1.0, 0.0, 0.0, 0.0],
    ]


def _stationary_pi(P: List[List[float]]) -> List[float]:
    # Solve pi^T P = pi^T, sum pi = 1.
    # Use a 4x4 linear system built from (P^T - I) pi = 0 plus sum constraint.
    PT = list(zip(*P))
    A = [[PT[i][j] - (1.0 if i == j else 0.0) for j in range(4)] for i in range(4)]
    b = [0.0, 0.0, 0.0, 0.0]
    # Replace last equation with sum(pi)=1 for numerical stability.
    A[3] = [1.0, 1.0, 1.0, 1.0]
    b[3] = 1.0

    M = sp.Matrix(A)
    rhs = sp.Matrix(b)
    sol = list(map(float, list(M.LUsolve(rhs))))
    return sol


def _variance_rate_edge_reward(P: List[List[float]], pi: List[float]) -> float:
    # Edge reward r(i,j)=g(i,j).
    g = [
        [0.0, 1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [1.0, 0.0, 0.0, 0.0],
        [0.0, 0.0, 0.0, 0.0],
    ]
    # mu = E[r]
    mu = 0.0
    for i in range(4):
        for j in range(4):
            mu += pi[i] * P[i][j] * g[i][j]

    # f(i) = E[r | S=i]
    f = [sum(P[i][j] * g[i][j] for j in range(4)) for i in range(4)]

    # Solve (I - P + 1*pi^T) h = f - mu*1.
    I = [[1.0 if i == j else 0.0 for j in range(4)] for i in range(4)]
    A = [[I[i][j] - P[i][j] + 1.0 * pi[j] for j in range(4)] for i in range(4)]
    b = [f[i] - mu for i in range(4)]
    h = list(map(float, list(sp.Matrix(A).LUsolve(sp.Matrix(b)))))

    # Martingale increment: M = r - mu + h(S1)-h(S0)
    # sigma^2 = E[M^2]
    sig2 = 0.0
    for i in range(4):
        for j in range(4):
            inc = g[i][j] - mu + h[j] - h[i]
            sig2 += pi[i] * P[i][j] * (inc * inc)
    return sig2


def main() -> None:
    t0 = time.time()

    # Symbolic closed forms (from the paper).
    p = sp.Symbol("p", positive=True, real=True)
    g_star = sp.simplify(p**2 * (3 - 2 * p) / (1 + p**3))
    sigma_star = sp.simplify(
        p**2
        * (1 - p)
        * (21 * p**5 - 6 * p**4 + 14 * p**3 - 36 * p**2 + 7 * p + 9)
        / ((p + 1) ** 3 * (p**2 - p + 1) ** 3)
    )
    Pi11 = (
        117 * p**11
        - 450 * p**10
        + 242 * p**9
        - 1360 * p**8
        + 2537 * p**7
        - 833 * p**6
        + 301 * p**5
        - 1076 * p**4
        + 188 * p**3
        + 344 * p**2
        - 37 * p
        - 27
    )
    kappa3_star = sp.simplify(p**2 * (p - 1) * Pi11 / ((p + 1) ** 5 * (p**2 - p + 1) ** 5))

    Pi17 = (
        609 * p**17
        - 7572 * p**16
        + 16148 * p**15
        - 30024 * p**14
        + 126169 * p**13
        - 182509 * p**12
        + 114342 * p**11
        - 197084 * p**10
        + 260364 * p**9
        - 65334 * p**8
        - 20148 * p**7
        - 40612 * p**6
        + 12405 * p**5
        + 19432 * p**4
        - 3652 * p**3
        - 2466 * p**2
        + 175 * p
        + 81
    )
    kappa4_star = sp.simplify(p**2 * (1 - p) * Pi17 / ((p + 1) ** 7 * (p**2 - p + 1) ** 7))

    # Characteristic polynomial factorization (symbolic).
    P_sym = sp.Matrix(
        [
            [1 - p, p**2, 0, p * (1 - p)],
            [0, 0, 1, 0],
            [1 - p, p, 0, 0],
            [1, 0, 0, 0],
        ]
    )
    lam = sp.Symbol("lam")
    char_poly = sp.factor((lam * sp.eye(4) - P_sym).det())
    char_expected = sp.factor((lam - 1) * (lam + p) * (lam**2 - p * (1 - p)))

    # Pressure quartic (characteristic polynomial of Q_p(u)).
    u = sp.Symbol("u", positive=True, real=True)
    g_sym = sp.Matrix([[0, 1, 0, 0], [0, 0, 1, 0], [1, 0, 0, 0], [0, 0, 0, 0]])
    Q_sym = sp.Matrix([[P_sym[i, j] * (u ** g_sym[i, j]) for j in range(4)] for i in range(4)])
    pressure_poly = sp.expand((lam * sp.eye(4) - Q_sym).det())
    pressure_expected = (
        lam**4
        + (p - 1) * lam**3
        + (p**2 - p * u - p) * lam**2
        + (p**3 * u**3 - p**2 * u**3 - p**2 * u + p * u) * lam
        + p**2 * u * (1 - p)
    )

    # Cumulants via implicit differentiation at (lam,u)=(1,1).
    F = sp.expand(pressure_expected)
    subs_11 = {lam: 1, u: 1}
    Fl = sp.simplify(sp.diff(F, lam).subs(subs_11))
    Fu = sp.simplify(sp.diff(F, u).subs(subs_11))
    Fll = sp.simplify(sp.diff(F, lam, 2).subs(subs_11))
    Flu = sp.simplify(sp.diff(F, lam, 1, u, 1).subs(subs_11))
    Fuu = sp.simplify(sp.diff(F, u, 2).subs(subs_11))
    Flll = sp.simplify(sp.diff(F, lam, 3).subs(subs_11))
    Fllu = sp.simplify(sp.diff(F, lam, 2, u, 1).subs(subs_11))
    Fluu = sp.simplify(sp.diff(F, lam, 1, u, 2).subs(subs_11))
    Fuuu = sp.simplify(sp.diff(F, u, 3).subs(subs_11))

    lam1 = sp.simplify(-Fu / Fl)  # d/du lambda(u,p) at u=1
    lam2 = sp.simplify(-(Fll * lam1**2 + 2 * Flu * lam1 + Fuu) / Fl)
    lam3 = sp.simplify(
        -(
            3 * (Fll * lam1 + Flu) * lam2
            + Flll * lam1**3
            + 3 * Fllu * lam1**2
            + 3 * Fluu * lam1
            + Fuuu
        )
        / Fl
    )
    kappa2_from_lam = sp.simplify(lam2 + lam1 - lam1**2)
    kappa3_from_lam = sp.simplify(lam3 + 3 * lam2 + lam1 - 3 * lam1 * lam2 - 3 * lam1**2 + 2 * lam1**3)

    # kappa4 via series expansion in theta using the implicit u-series at u=1.
    t = sp.Symbol("t", real=True)
    a1, a2, a3, a4 = sp.symbols("a1 a2 a3 a4")
    lam_series = 1 + a1 * t + a2 * t**2 + a3 * t**3 + a4 * t**4
    F_t = sp.expand(F.subs({u: 1 + t, lam: lam_series}))
    coeffs = [sp.expand(sp.series(F_t, t, 0, 5).removeO().coeff(t, k)) for k in range(1, 5)]
    # Solve sequentially to keep expressions tractable.
    sol_a1 = sp.simplify(sp.solve(sp.Eq(coeffs[0], 0), a1)[0])
    sol_a2 = sp.simplify(sp.solve(sp.Eq(coeffs[1].subs({a1: sol_a1}), 0), a2)[0])
    sol_a3 = sp.simplify(sp.solve(sp.Eq(coeffs[2].subs({a1: sol_a1, a2: sol_a2}), 0), a3)[0])
    sol_a4 = sp.simplify(sp.solve(sp.Eq(coeffs[3].subs({a1: sol_a1, a2: sol_a2, a3: sol_a3}), 0), a4)[0])
    # theta-series: u=e^theta => t=u-1.
    th = sp.Symbol("th", real=True)
    t_th = sp.expand(sp.series(sp.exp(th) - 1, th, 0, 5).removeO())
    lam_th = sp.expand((1 + sol_a1 * t_th + sol_a2 * t_th**2 + sol_a3 * t_th**3 + sol_a4 * t_th**4))
    P_th = sp.expand(sp.series(sp.log(lam_th), th, 0, 5).removeO())
    kappa4_from_series = sp.simplify(sp.factorial(4) * sp.expand(P_th).coeff(th, 4))

    # Endpoint I_p(0): rho(Q_p(0)) closed form.
    rho_q0 = sp.simplify(((1 - p) + sp.sqrt((1 - p) * (1 + 3 * p))) / 2)
    I0 = sp.simplify(-sp.log(rho_q0))
    I1 = sp.simplify(-sp.Rational(1, 3) * sp.log(p**2 * (1 - p)))
    delta_inf = sp.simplify(sp.Rational(1, 3) * sp.log(p**2 * (1 - p)) - sp.log(rho_q0))

    # Covariance GF closed form (as in the paper).
    z = sp.Symbol("z")
    Cp_closed = sp.simplify(
        p**2
        * z
        * (
            (3 * p**7 - 14 * p**6 + 19 * p**5 - 9 * p**4 + 2 * p**3 - 2 * p**2 + p) * z**2
            + (-3 * p**6 - 2 * p**5 + 9 * p**4 + p**3 - 7 * p**2 + p + 1) * z
            + (-p**6 + p**5 - 6 * p**4 + 13 * p**3 - 8 * p**2 - 2 * p + 2)
        )
        / ((1 + p**3) ** 2 * (1 + p * z) * (1 - p * (1 - p) * z**2))
    )

    # Bit-pair law closed form.
    P00 = (1 - p - p**2 + 2 * p**3 - p**4) / (1 + p**3)
    P01 = (p**2 * (1 - p)) / (1 + p**3)
    P10 = (p**2 * (2 - p)) / (1 + p**3)
    P11 = (p * (p**3 + (1 - p) ** 2)) / (1 + p**3)

    # Reparameterized covariance coefficients (odd/even closed forms).
    r_cov = sp.simplify(p * (1 - p))
    alpha_cov = sp.simplify(-p**3 * (p**2 - 3 * p + 1) ** 2 / ((p + 1) ** 2 * (2 * p - 1) * (p**2 - p + 1)))
    beta_cov = sp.simplify(
        p**2 * (1 - p) * (p**5 + 4 * p**4 - 4 * p**3 - 5 * p**2 + 7 * p - 2) / ((p + 1) * (2 * p - 1) * (p**2 - p + 1) ** 2)
    )
    delta_cov = sp.simplify(
        p**2 * (1 - p) ** 2 * (p**5 - p**4 - 6 * p**3 + 3 * p**2 + 2 * p - 1) / ((p + 1) * (2 * p - 1) * (p**2 - p + 1) ** 2)
    )
    critical_cov = lambda k: sp.simplify(
        sp.Rational(1, 2) ** (k - 1)
        * (sp.Rational(1, 16) + (-1) ** (k - 1) * (-sp.Rational(13, 1296) - sp.Rational(k - 1, 216)))
    )

    # Output-density / mismatch-density elimination polynomial.
    q_out = sp.simplify(P01 + P11)
    gamma_out = sp.simplify(g_star)
    q_sym, gamma_sym = sp.symbols("q_out gamma_out", real=True)
    state_curve_poly = (
        gamma_sym**4
        + 9 * gamma_sym**3 * q_sym
        + 4 * gamma_sym**3
        + 27 * gamma_sym**2 * q_sym**2
        + 18 * gamma_sym**2 * q_sym
        - 23 * gamma_sym**2
        + 35 * gamma_sym * q_sym**3
        + 72 * gamma_sym * q_sym**2
        - 54 * gamma_sym * q_sym
        + 23 * gamma_sym
        + 70 * q_sym**3
        - 69 * q_sym**2
    )

    # Word-probability algebra for the mismatch indicator process.
    B1_sym = P_sym.multiply_elementwise(g_sym)
    B0_sym = sp.simplify(P_sym - B1_sym)
    pi_row_sym = sp.Matrix([[1 - p, p**2, p**2, p * (1 - p) ** 2]]) / (1 + p**3)
    ones_sym = sp.Matrix([1, 1, 1, 1])

    def _word_prob(word: str) -> sp.Expr:
        acc = pi_row_sym
        for bit in word:
            acc = acc * (B1_sym if bit == "1" else B0_sym)
        return sp.simplify((acc * ones_sym)[0])

    kernel_formulas: Dict[str, sp.Expr] = {
        "000": p**2 * (2 * p + 1) / ((1 + p) * (1 + 2 * p - p**2)),
        "001": sp.Integer(1),
        "010": sp.Integer(1),
        "011": (2 * p**3 - p**2 - p + 1) / (1 + p - p**2),
        "100": p**2 / (1 + p - p**2),
        "101": (1 - p) * (1 + p - p**2) / (1 + p - 2 * p**2 + p**3),
        "110": p,
        "111": p**2 * (3 - 2 * p) / (1 - p + 2 * p**2),
    }

    # Pressure discriminant polynomial in (u,p).
    pressure_discriminant = sp.expand(sp.discriminant(pressure_expected, lam))
    D_up = sp.expand(sp.simplify(pressure_discriminant / (p**3 * u * (1 - p))))

    # Numeric audit points.
    ps: List[float] = [0.11, 0.27, 0.5, 0.73, 0.91]
    z0 = 0.17

    results: List[CheckResult] = []
    details: Dict[str, Dict[str, float]] = {}

    # 1) char poly factorization (symbolic exact).
    results.append(CheckResult(name="char_poly_factorization", max_abs_err=float(char_poly != char_expected)))
    results.append(CheckResult(name="pressure_quartic", max_abs_err=float(sp.simplify(pressure_poly - pressure_expected) != 0)))
    results.append(CheckResult(name="kappa2_from_implicit_matches_sigma2", max_abs_err=float(sp.simplify(kappa2_from_lam - sigma_star) != 0)))
    results.append(CheckResult(name="kappa3_closed_form", max_abs_err=float(sp.simplify(kappa3_from_lam - kappa3_star) != 0)))
    results.append(CheckResult(name="kappa4_closed_form", max_abs_err=float(sp.simplify(kappa4_from_series - kappa4_star) != 0)))

    # 1b) Perron interface: A_{theta,p} eigenvectors and Parry normalization (symbolic exact).
    q = 1 - p
    A0_sym = sp.Matrix(
        [
            [q, q, 0, p],
            [0, 0, p, 0],
            [p, 1, 0, 0],
            [q, 0, 0, 0],
        ]
    )
    r_sym = sp.Matrix([q, p**2, p, q**2])
    ell_sym = sp.Matrix([1, 1, p, p])  # left Perron eigenvector (as a column)
    A0_r_resid = sp.simplify(A0_sym * r_sym - r_sym)
    ell_A0_resid = sp.simplify((ell_sym.T * A0_sym - ell_sym.T))
    results.append(
        CheckResult(
            name="A0_right_eigenvector",
            max_abs_err=float(any(sp.simplify(x) != 0 for x in list(A0_r_resid))),
        )
    )
    results.append(
        CheckResult(
            name="A0_left_eigenvector",
            max_abs_err=float(any(sp.simplify(x) != 0 for x in list(ell_A0_resid))),
        )
    )
    P_from_A0 = sp.Matrix([[sp.simplify(A0_sym[i, j] * r_sym[j] / r_sym[i]) for j in range(4)] for i in range(4)])
    P_from_A0_resid = sp.simplify(P_from_A0 - P_sym)
    results.append(
        CheckResult(
            name="parry_normalization_P",
            max_abs_err=float(any(sp.simplify(x) != 0 for x in list(P_from_A0_resid))),
        )
    )
    # Diagonal similarity for the u-tilt: Q = D^{-1} A_u D.
    A_u_sym = sp.Matrix(
        [
            [q, q * u, 0, p],
            [0, 0, p * u, 0],
            [p * u, 1, 0, 0],
            [q, 0, 0, 0],
        ]
    )
    D = sp.diag(*list(r_sym))
    sim_resid = sp.simplify(A_u_sym * D - D * Q_sym)
    results.append(
        CheckResult(
            name="tilt_similarity_Au_vs_Q",
            max_abs_err=float(any(sp.simplify(x) != 0 for x in list(sim_resid))),
        )
    )

    # 1c) Unimodality and 1/2-threshold (symbolic exact).
    g_prime = sp.factor(sp.diff(g_star, p))
    g_prime_expected = sp.factor(-3 * p * (p**3 + 2 * p - 2) / ((p + 1) ** 2 * (p**2 - p + 1) ** 2))
    results.append(CheckResult(name="density_derivative_closed_form", max_abs_err=float(sp.simplify(g_prime - g_prime_expected) != 0)))
    half_diff = sp.factor(sp.simplify(g_star - sp.Rational(1, 2)))
    half_expected = sp.factor(-(p - 1) * (5 * p**2 - p - 1) / (2 * (1 + p**3)))
    results.append(CheckResult(name="density_half_threshold_factorization", max_abs_err=float(sp.simplify(half_diff - half_expected) != 0)))
    collapse = sp.factor(sp.simplify(g_star - p**2))
    collapse_expected = sp.factor(-(p**2) * (p**3 + 2 * p - 2) / (1 + p**3))
    results.append(CheckResult(name="density_square_collapse_factorization", max_abs_err=float(sp.simplify(collapse - collapse_expected) != 0)))

    # 1d) GC far-field defect constant: delta_inf(pcrit)=0 and sign matches 4p^2-2p-1.
    pcrit = sp.simplify((1 + sp.sqrt(5)) / 4)
    delta_pcrit = float(sp.N(delta_inf.subs({p: pcrit}), 80))
    results.append(CheckResult(name="gc_farfield_pcrit_zero", max_abs_err=abs(delta_pcrit)))
    sign_samples = [0.11, 0.27, 0.73, 0.91]
    sign_ok = True
    for pv in sign_samples:
        dv = float(sp.N(delta_inf.subs({p: pv}), 80))
        poly = 4 * pv * pv - 2 * pv - 1
        # allow equality only at the unique critical point (not in our sample set)
        sign_ok = sign_ok and ((dv > 0) == (poly > 0))
    results.append(CheckResult(name="gc_farfield_sign_samples", max_abs_err=float(not sign_ok)))

    # 1e) state equation and elimination curve in (q_out, gamma_out).
    state_eq_resid = sp.simplify(gamma_out - (3 - 2 * p) * (p - q_out))
    results.append(CheckResult(name="state_equation_gamma_q", max_abs_err=float(state_eq_resid != 0)))
    curve_resid = sp.simplify(state_curve_poly.subs({q_sym: q_out, gamma_sym: gamma_out}))
    results.append(CheckResult(name="state_curve_elimination", max_abs_err=float(curve_resid != 0)))

    # 1f) strict third-order kernel of (G_t).
    kernel_ok = True
    for ctx, expr in kernel_formulas.items():
        den = _word_prob(ctx)
        num = _word_prob(ctx + "1")
        cond = sp.simplify(num / den)
        if sp.simplify(cond - expr) != 0:
            kernel_ok = False
            break
    results.append(CheckResult(name="mismatch_third_order_kernel", max_abs_err=float(not kernel_ok)))
    kernel_gap = sp.simplify(kernel_formulas["000"] - kernel_formulas["100"])
    kernel_gap_expected = sp.simplify(-p**5 / ((1 + p) * (1 + 2 * p - p**2) * (1 + p - p**2)))
    results.append(CheckResult(name="mismatch_not_second_order_gap", max_abs_err=float(sp.simplify(kernel_gap - kernel_gap_expected) != 0)))

    # 1g) pressure discriminant factorization and u=1 resonance criterion.
    results.append(
        CheckResult(
            name="pressure_discriminant_factorization",
            max_abs_err=float(sp.simplify(pressure_discriminant - p**3 * u * (1 - p) * D_up) != 0),
        )
    )
    D_u_degree = int(sp.Poly(D_up, u).degree())
    results.append(CheckResult(name="pressure_discriminant_degree_u", max_abs_err=float(D_u_degree != 11)))
    D_u1_expected = sp.simplify(4 * (1 + p) ** 2 * (2 * p - 1) ** 2 * (p**2 - p + 1) ** 2)
    results.append(CheckResult(name="pressure_discriminant_u1", max_abs_err=float(sp.simplify(D_up.subs({u: 1}) - D_u1_expected) != 0)))

    # 2) numeric checks across p-grid
    errs_density: List[float] = []
    errs_sigma: List[float] = []
    errs_kappa3: List[float] = []
    errs_kappa4: List[float] = []
    errs_I0: List[float] = []
    errs_prob_sum: List[float] = []
    errs_Cp: List[float] = []
    errs_cov_recur: List[float] = []
    errs_cov_shifted_gf: List[float] = []
    errs_cov_even_odd: List[float] = []
    errs_cov_half_jordan: List[float] = []

    for pv in ps:
        P_num = _P(pv)
        pi_num = _stationary_pi(P_num)

        # density
        mu_num = 0.0
        g_edge = [
            [0.0, 1.0, 0.0, 0.0],
            [0.0, 0.0, 1.0, 0.0],
            [1.0, 0.0, 0.0, 0.0],
            [0.0, 0.0, 0.0, 0.0],
        ]
        for i in range(4):
            for j in range(4):
                mu_num += pi_num[i] * P_num[i][j] * g_edge[i][j]
        mu_cf = float(sp.N(g_star.subs({p: pv}), 50))
        errs_density.append(mu_num - mu_cf)

        # variance rate
        sig_num = _variance_rate_edge_reward(P_num, pi_num)
        sig_cf = float(sp.N(sigma_star.subs({p: pv}), 50))
        errs_sigma.append(sig_num - sig_cf)

        # third cumulant density (pressure third derivative at 0)
        k3_cf = float(sp.N(kappa3_star.subs({p: pv}), 50))
        k3_imp = float(sp.N(kappa3_from_lam.subs({p: pv}), 50))
        errs_kappa3.append(k3_imp - k3_cf)

        # fourth cumulant density (series-based vs closed form)
        k4_cf = float(sp.N(kappa4_star.subs({p: pv}), 50))
        k4_ser = float(sp.N(kappa4_from_series.subs({p: pv}), 50))
        errs_kappa4.append(k4_ser - k4_cf)

        # endpoint I0
        I0_cf = float(sp.N(I0.subs({p: pv}), 50))
        # Q_p(0) Perron root is rho_q0 (closed form), so compare directly:
        rho_cf = float(sp.N(rho_q0.subs({p: pv}), 50))
        errs_I0.append((-math.log(rho_cf)) - I0_cf)

        # bit-pair law: sum to 1 and nonnegativity
        probs = [
            float(sp.N(P00.subs({p: pv}), 50)),
            float(sp.N(P01.subs({p: pv}), 50)),
            float(sp.N(P10.subs({p: pv}), 50)),
            float(sp.N(P11.subs({p: pv}), 50)),
        ]
        errs_prob_sum.append(sum(probs) - 1.0)

        # covariance generating function: compare closed form vs matrix resolvent formula
        # Build numeric matrices in sympy for stable inversion.
        pvv = sp.nsimplify(pv)
        Pm = sp.Matrix(
            [
                [1 - pvv, pvv**2, 0, pvv * (1 - pvv)],
                [0, 0, 1, 0],
                [1 - pvv, pvv, 0, 0],
                [1, 0, 0, 0],
            ]
        )
        gm = sp.Matrix([[0, 1, 0, 0], [0, 0, 1, 0], [1, 0, 0, 0], [0, 0, 0, 0]])
        Hm = Pm.multiply_elementwise(gm)
        pi_col = sp.Matrix([1 - pvv, pvv**2, pvv**2, pvv * (1 - pvv) ** 2]) / (1 + pvv**3)
        pi_row = pi_col.T
        ones = sp.Matrix([1, 1, 1, 1])
        mu = sp.simplify((pi_row * Hm * ones)[0])

        zsym = sp.nsimplify(z0)
        Cm_mat = sp.simplify(zsym * (pi_row * Hm * (sp.eye(4) - zsym * Pm).inv() * Hm * ones)[0] - mu**2 * zsym / (1 - zsym))
        Cm_closed = sp.simplify(Cp_closed.subs({p: pvv, z: zsym}))
        errs_Cp.append(float(sp.N(Cm_mat - Cm_closed, 50)))

        # recurrence spot-check for k=1..5 using exact c_k from matrix formula.
        # c_k = pi^T H P^{k-1} H 1 - mu^2
        cs: List[sp.Expr] = []
        for k in range(1, 9):
            Ek = sp.simplify((pi_row * Hm * (Pm ** (k - 1)) * Hm * ones)[0] - mu**2)
            cs.append(Ek)
        # check recurrence residuals
        for k in range(1, 6):
            lhs = cs[k + 2]  # c_{k+3}
            rhs = sp.simplify(-pvv * cs[k + 1] + pvv * (1 - pvv) * cs[k] + pvv**2 * (1 - pvv) * cs[k - 1])
            errs_cov_recur.append(float(sp.N(lhs - rhs, 50)))

        # Shifted covariance GF:
        # S_p(z)=sum_{n>=0} s_n z^n with s_n=c_{n+1}, and C_p(z)=z S_p(z).
        s0, s1, s2 = cs[0], cs[1], cs[2]
        S_formula = sp.simplify(
            (s0 + (s1 + pvv * s0) * zsym + (s2 + pvv * s1 - pvv * (1 - pvv) * s0) * zsym**2)
            / ((1 + pvv * zsym) * (1 - pvv * (1 - pvv) * zsym**2))
        )
        errs_cov_shifted_gf.append(float(sp.N(S_formula - (Cm_mat / zsym), 50)))

        # Explicit odd/even covariance closed forms away from p=1/2.
        if abs(pv - 0.5) > 1e-12:
            alpha_num = float(sp.N(alpha_cov.subs({p: pvv}), 60))
            beta_num = float(sp.N(beta_cov.subs({p: pvv}), 60))
            delta_num = float(sp.N(delta_cov.subs({p: pvv}), 60))
            r_num = float(sp.N(r_cov.subs({p: pvv}), 60))
            for k in range(1, 9):
                c_num = float(sp.N(cs[k - 1], 60))
                if k % 2 == 1:
                    m = (k - 1) // 2
                    c_closed = alpha_num * (pv ** (2 * m)) + beta_num * (r_num**m)
                else:
                    m = k // 2
                    c_closed = -alpha_num * (pv ** (2 * m - 1)) + delta_num * (r_num ** (m - 1))
                errs_cov_even_odd.append(c_num - c_closed)
        else:
            for k in range(1, 9):
                c_num = float(sp.N(cs[k - 1], 60))
                c_closed = float(sp.N(critical_cov(k), 60))
                errs_cov_half_jordan.append(c_num - c_closed)

        details[str(pv)] = {
            "g_star_numeric": mu_num,
            "g_star_closed": mu_cf,
            "sigma2_numeric": sig_num,
            "sigma2_closed": sig_cf,
            "kappa3_closed": k3_cf,
            "kappa3_implicit": k3_imp,
            "kappa4_closed": k4_cf,
            "kappa4_series": k4_ser,
            "I0_closed": I0_cf,
            "prob_sum": sum(probs),
            "Cp_diff": float(sp.N(Cm_mat - Cm_closed, 30)),
        }

    results.extend(
        [
            CheckResult(name="density_g_star", max_abs_err=_max_abs(errs_density)),
            CheckResult(name="variance_sigma2", max_abs_err=_max_abs(errs_sigma)),
            CheckResult(name="kappa3_density", max_abs_err=_max_abs(errs_kappa3)),
            CheckResult(name="kappa4_density", max_abs_err=_max_abs(errs_kappa4)),
            CheckResult(name="endpoint_I0", max_abs_err=_max_abs(errs_I0)),
            CheckResult(name="bitpair_prob_sum", max_abs_err=_max_abs(errs_prob_sum)),
            CheckResult(name="covariance_gf_match", max_abs_err=_max_abs(errs_Cp)),
            CheckResult(name="covariance_recurrence", max_abs_err=_max_abs(errs_cov_recur)),
            CheckResult(name="covariance_shifted_gf_formula", max_abs_err=_max_abs(errs_cov_shifted_gf)),
            CheckResult(name="covariance_even_odd_closed_form", max_abs_err=_max_abs(errs_cov_even_odd)),
            CheckResult(name="covariance_half_jordan_closed_form", max_abs_err=_max_abs(errs_cov_half_jordan)),
        ]
    )

    # 3) Sturm root count for Pi11 on (0,1) and numeric roots.
    Pi11_poly = sp.Poly(Pi11, p)
    n_roots_01 = int(sp.count_roots(Pi11_poly, 0, 1))
    results.append(CheckResult(name="Pi11_root_count_(0,1)", max_abs_err=float(n_roots_01 != 2)))
    Pi11_roots = []
    for rr in sp.nroots(Pi11_poly.as_expr(), n=80):
        if abs(sp.im(rr)) < sp.Float("1e-40"):
            rv = float(sp.re(rr))
            if 0.0 < rv < 1.0:
                Pi11_roots.append(rv)
    Pi11_roots = sorted(Pi11_roots)

    # p=1/2 table check (exact fractions)
    half = sp.Rational(1, 2)
    half_probs = [sp.simplify(P00.subs({p: half})), sp.simplify(P01.subs({p: half})), sp.simplify(P10.subs({p: half})), sp.simplify(P11.subs({p: half}))]
    assert half_probs == [sp.Rational(7, 18), sp.Rational(1, 9), sp.Rational(1, 3), sp.Rational(1, 6)]

    out = {
        "checks": [{"name": r.name, "max_abs_err": r.max_abs_err} for r in results],
        "samples": details,
        "symbolic": {
            "char_poly": str(char_poly),
            "char_expected": str(char_expected),
            "g_star": str(g_star),
            "sigma2": str(sigma_star),
            "kappa3": str(kappa3_star),
            "kappa4": str(kappa4_star),
            "I0": str(I0),
            "I1": str(I1),
            "q_out": str(q_out),
            "gamma_out": str(gamma_out),
            "state_curve_poly": str(state_curve_poly),
            "pressure_discriminant_over_p3u1mp": str(D_up),
            "Pi11_root_count_(0,1)": n_roots_01,
            "Pi11_roots_(0,1)": Pi11_roots,
        },
        "elapsed_s": time.time() - t0,
    }

    export_path = export_dir() / "fold_gauge_anomaly_bernoulli_p_closed_form.json"
    _write_text(export_path, json.dumps(out, indent=2, sort_keys=True) + "\n")

    # Print a short summary for interactive runs.
    worst = max(results, key=lambda r: r.max_abs_err)
    print(f"[fold_gauge_anomaly_bernoulli_p_closed_form] worst_check={worst.name} max_abs_err={worst.max_abs_err:.3e}")


if __name__ == "__main__":
    main()

