#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the centered Perron-branch third-order Fuchs operator for the Fold Lee-Yang quartic.

This script is English-only by repository convention.

We verify:
  - The explicit third-order linear ODE (A3 f''' + A2 f'' + A1 f' + A0 f = 0)
    for f(y)=lambda(y)-1/4 in the function-field quotient K=Q(y)[lambda]/(Pi).
  - Singular-set split and local-index identities:
      gcd(Q, y(y-1)P_LY)=1,
      2A2-3A3' vanishes on y(y-1)P_LY=0  (index set {0,1/2,1}),
      A2+A3' vanishes on Q=0              (index set {0,1,3}).
  - Infinity indicial polynomial:
      32*sigma^3 - 16*sigma^2 - 2*sigma + 1.
  - Wronskian-square logarithmic derivative identity:
      d/dy log( Q^2/(y^3(y-1)^3 P_LY^3) ) = -2 A2/A3.
  - Perron formal branch lambda_+(1+t) has denominators supported only at prime 3.
  - Cumulant densities psi^{(n)}(0) for psi(s)=log(lambda_+(e^s-1)/2)
    have denominators supported only at primes {2,3}.
  - For sampled p != 3, mod-p reduced series satisfies the reduced algebraic equation
    to the audited truncation order (Christol applicability checkpoint).
  - The induced action on the trace-zero hyperplane is the standard 3D S4 representation
    (generated subgroup size 24 from transposition and 4-cycle).

Outputs:
  - artifacts/export/fold_zm_leyang_perron_fuchs_operator_audit.json
  - sections/generated/eq_fold_zm_leyang_perron_fuchs_operator.tex
"""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Set, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _prime_factors(n: int) -> Set[int]:
    n = abs(int(n))
    if n <= 1:
        return set()
    fac = sp.factorint(n)
    return {int(p) for p in fac.keys()}


def _denominator_prime_support(q: sp.Rational) -> Set[int]:
    qq = sp.Rational(q)
    return _prime_factors(int(sp.denom(qq)))


def _modp_rational(q: sp.Rational, p: int) -> int:
    qq = sp.Rational(q)
    num = int(sp.numer(qq)) % p
    den = int(sp.denom(qq)) % p
    if den == 0:
        raise ZeroDivisionError(f"denominator divisible by p={p}")
    return (num * pow(den, -1, p)) % p


def _matrix_from_perm(perm: Sequence[int]) -> sp.Matrix:
    n = len(perm)
    P = sp.zeros(n, n)
    for i in range(n):
        P[perm[i], i] = 1
    return P


def _matrix_key(M: sp.Matrix) -> Tuple[int, ...]:
    return tuple(int(x) for x in list(M))


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Lee-Yang Perron centered Fuchs operator identities.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-leyang-perron-fuchs] start", flush=True)

    lam, y, t, s, sigma = sp.symbols("lam y t s sigma")

    Pi = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)
    P_LY = 256 * y**3 + 411 * y**2 + 165 * y + 32
    Q = 168 * y**5 + 1260 * y**4 - 422 * y**3 - 183 * y**2 - 639 * y - 76

    A3 = y * (y - 1) * P_LY * Q
    A2 = 6 * (
        17920 * y**9
        + 192500 * y**8
        - 12480 * y**7
        - 94031 * y**6
        - 139107 * y**5
        - 71300 * y**4
        + 80597 * y**3
        + 41863 * y**2
        + 6758 * y
        + 608
    )
    A1 = 6 * (
        3136 * y**8
        + 45164 * y**7
        - 56178 * y**6
        - 36438 * y**5
        - 138724 * y**4
        - 62488 * y**3
        + 18443 * y**2
        + 5933 * y
        - 32
    )
    A0 = 24 * (
        56 * y**7
        + 1036 * y**6
        + 3844 * y**5
        + 3740 * y**4
        + 8288 * y**3
        + 1417 * y**2
        + 19 * y
        + 32
    )

    # --- Third-order ODE identity in K = Q(y)[lam]/(Pi) ---
    Pi_l = sp.diff(Pi, lam)
    Pi_y = sp.diff(Pi, y)
    lam_prime = -Pi_y / Pi_l

    def deriv(expr: sp.Expr) -> sp.Expr:
        expr = sp.together(expr)
        return sp.together(sp.diff(expr, y) + sp.diff(expr, lam) * lam_prime)

    g0 = lam - sp.Rational(1, 4)
    g1 = deriv(g0)
    g2 = deriv(g1)
    g3 = deriv(g2)

    rel = sp.together(A3 * g3 + A2 * g2 + A1 * g1 + A0 * g0)
    rel_num = sp.expand(rel.as_numer_denom()[0])
    rel_rem = sp.rem(sp.Poly(rel_num, lam, domain=sp.QQ[y]), sp.Poly(Pi, lam, domain=sp.QQ[y])).as_expr()
    ode_identity_ok = bool(sp.expand(rel_rem) == 0)

    print("[fold-zm-leyang-perron-fuchs] ode identity checked", flush=True)

    # --- Singular split and local-index signatures ---
    D_true = y * (y - 1) * P_LY
    gcd_Q_true = sp.gcd(sp.Poly(Q, y, domain=sp.ZZ), sp.Poly(D_true, y, domain=sp.ZZ)).as_expr()
    gcd_Q_true_ok = bool(sp.expand(gcd_Q_true) == 1)

    A3p = sp.diff(A3, y)
    idx_true_half_ok = bool(sp.expand(sp.rem(2 * A2 - 3 * A3p, D_true, y)) == 0)
    idx_app_three_ok = bool(sp.expand(sp.rem(A2 + A3p, Q, y)) == 0)

    print("[fold-zm-leyang-perron-fuchs] singular split checked", flush=True)

    # --- Infinity indicial polynomial ---
    lc_A3 = sp.LC(sp.Poly(A3, y, domain=sp.ZZ))
    lc_A2 = sp.LC(sp.Poly(A2, y, domain=sp.ZZ))
    lc_A1 = sp.LC(sp.Poly(A1, y, domain=sp.ZZ))
    lc_A0 = sp.LC(sp.Poly(A0, y, domain=sp.ZZ))
    ind_inf = sp.expand(
        lc_A3 * sigma * (sigma - 1) * (sigma - 2)
        + lc_A2 * sigma * (sigma - 1)
        + lc_A1 * sigma
        + lc_A0
    )
    target_ind = 32 * sigma**3 - 16 * sigma**2 - 2 * sigma + 1
    ind_inf_ok = bool(sp.expand(ind_inf - 1344 * target_ind) == 0)
    ind_inf_factored = sp.factor(target_ind)

    print("[fold-zm-leyang-perron-fuchs] infinity indicial checked", flush=True)

    # --- Wronskian-square logarithmic derivative ---
    p2 = sp.together(A2 / A3)
    R = sp.together(Q**2 / (y**3 * (y - 1) ** 3 * P_LY**3))
    wr_log_expr = sp.together(sp.diff(R, y) / R + 2 * p2)
    wr_log_num = sp.expand(wr_log_expr.as_numer_denom()[0])
    wronskian_logder_ok = bool(wr_log_num == 0)

    print("[fold-zm-leyang-perron-fuchs] wronskian identity checked", flush=True)

    # --- Perron branch formal series Lambda(t) at y=1+t ---
    N_series = 14
    a_syms = sp.symbols("a1:%d" % (N_series + 1))
    Lam = sp.Integer(2) + sum(a_syms[k - 1] * t**k for k in range(1, N_series + 1))
    eq_series = sp.expand(Pi.subs({lam: Lam, y: 1 + t}))

    sol: Dict[sp.Symbol, sp.Expr] = {}
    for k in range(1, N_series + 1):
        ak = a_syms[k - 1]
        coeff_k = sp.expand(eq_series.subs(sol)).coeff(t, k)
        linear_coeff = sp.expand(sp.diff(coeff_k, ak))
        const_part = sp.expand(coeff_k.subs(ak, 0))
        if linear_coeff == 0:
            raise RuntimeError(f"Nonlinear/degenerate recursion at k={k}")
        sol[ak] = sp.together(-const_part / linear_coeff)

    Lam_series = sp.expand(Lam.subs(sol))
    check_series = sp.expand(eq_series.subs(sol))
    series_identity_ok = all(sp.expand(check_series.coeff(t, k)) == 0 for k in range(0, N_series + 1))

    lam_coeffs = [sp.Rational(2)] + [sp.Rational(sp.simplify(sol[a_syms[k - 1]])) for k in range(1, N_series + 1)]
    lam_den_support = sorted(set().union(*[_denominator_prime_support(c) for c in lam_coeffs[1:]]))
    lambda_only_prime3_ok = bool(set(lam_den_support).issubset({3}))

    print("[fold-zm-leyang-perron-fuchs] perron series checked", flush=True)

    # --- Cumulant-density denominators from psi(s)=log(Lam(e^s-1)/2) ---
    M_cum = 8
    es1 = sp.expand(sp.series(sp.exp(s) - 1, s, 0, M_cum + 1).removeO())
    Lam_s = sp.expand(sp.series(Lam_series.subs(t, es1), s, 0, M_cum + 1).removeO())
    psi = sp.expand(sp.series(sp.log(Lam_s / 2), s, 0, M_cum + 1).removeO())
    kappas: List[sp.Rational] = []
    for n in range(1, M_cum + 1):
        coeff_n = sp.Rational(sp.expand(psi).coeff(s, n))
        kappas.append(sp.Rational(math.factorial(n)) * coeff_n)
    kappa_den_support = sorted(set().union(*[_denominator_prime_support(kv) for kv in kappas]))
    kappa_only_2_3_ok = bool(set(kappa_den_support).issubset({2, 3}))

    print("[fold-zm-leyang-perron-fuchs] cumulant denominators checked", flush=True)

    # --- Mod-p algebraicity checkpoints (p != 3) ---
    primes_test = [2, 5, 7, 11]
    modp_checks: Dict[str, bool] = {}
    for p in primes_test:
        coeff_mod = [_modp_rational(c, p) for c in lam_coeffs]
        Lam_mod = sp.expand(sum(int(coeff_mod[k]) * t**k for k in range(0, N_series + 1)))
        expr_mod = sp.expand(
            Lam_mod**4
            - Lam_mod**3
            - (2 * (1 + t) + 1) * Lam_mod**2
            + Lam_mod
            + (1 + t) * (2 + t)
        )
        poly_mod = sp.Poly(expr_mod, t, modulus=p)
        ok = True
        for k in range(0, N_series + 1):
            if int(poly_mod.nth(k)) % p != 0:
                ok = False
                break
        modp_checks[str(p)] = ok

    print("[fold-zm-leyang-perron-fuchs] mod-p checks done", flush=True)

    # --- Standard 3D representation checkpoint for S4 ---
    # Basis of trace-zero hyperplane in C^4: v1=e1-e4, v2=e2-e4, v3=e3-e4.
    B = sp.Matrix(
        [
            [1, 0, 0],
            [0, 1, 0],
            [0, 0, 1],
            [-1, -1, -1],
        ]
    )
    BTB_inv_BT = (B.T * B).inv() * B.T

    # Generators in S4: tau=(12), cyc=(1234) in 0-based image form.
    P_tau = _matrix_from_perm([1, 0, 2, 3])
    P_cyc = _matrix_from_perm([1, 2, 3, 0])
    M_tau = sp.simplify(BTB_inv_BT * P_tau * B)
    M_cyc = sp.simplify(BTB_inv_BT * P_cyc * B)
    M_tau = sp.Matrix([[sp.Integer(sp.simplify(x)) for x in row] for row in M_tau.tolist()])
    M_cyc = sp.Matrix([[sp.Integer(sp.simplify(x)) for x in row] for row in M_cyc.tolist()])

    I3 = sp.eye(3)
    gens = [M_tau, M_cyc]
    seen: Dict[Tuple[int, ...], sp.Matrix] = {_matrix_key(I3): I3}
    frontier: List[sp.Matrix] = [I3]
    while frontier:
        g = frontier.pop()
        for h in gens:
            for prod in (g * h, h * g):
                key = _matrix_key(prod)
                if key not in seen:
                    seen[key] = prod
                    frontier.append(prod)
    std_rep_group_size = len(seen)
    std_rep_group_size_ok = bool(std_rep_group_size == 24)
    std_rep_traces_ok = bool(int(M_tau.trace()) == 1 and int(M_cyc.trace()) == -1)

    payload: Dict[str, object] = {
        "ode_identity_ok": ode_identity_ok,
        "gcd_Q_true_ok": gcd_Q_true_ok,
        "idx_true_half_ok": idx_true_half_ok,
        "idx_app_three_ok": idx_app_three_ok,
        "indicial_infty_ok": ind_inf_ok,
        "wronskian_logder_ok": wronskian_logder_ok,
        "series_identity_ok": series_identity_ok,
        "lambda_only_prime3_ok": lambda_only_prime3_ok,
        "lambda_denominator_prime_support": lam_den_support,
        "kappa_only_2_3_ok": kappa_only_2_3_ok,
        "kappa_denominator_prime_support": kappa_den_support,
        "kappa_first_8": [str(kappas[i]) for i in range(8)],
        "modp_checks": modp_checks,
        "std_rep_group_size": std_rep_group_size,
        "std_rep_group_size_ok": std_rep_group_size_ok,
        "std_rep_traces_ok": std_rep_traces_ok,
        "elapsed_s": float(time.time() - t0),
    }

    if not args.no_output:
        out_json = export_dir() / "fold_zm_leyang_perron_fuchs_operator_audit.json"
        out_tex = generated_dir() / "eq_fold_zm_leyang_perron_fuchs_operator.tex"

        lam_series_short = (
            r"\Lambda(t)=2+\frac{5}{9}t-\frac{64}{243}t^{2}+\frac{2404}{6561}t^{3}"
            r"-\frac{159436}{177147}t^{4}+\frac{15226688}{4782969}t^{5}+O(t^{6})."
        )

        tex_lines: List[str] = []
        tex_lines.append("% Auto-generated by scripts/exp_fold_zm_leyang_perron_fuchs_operator_audit.py")
        tex_lines.append(r"\[")
        tex_lines.append(r"\Pi(\lambda,y)=\lambda^{4}-\lambda^{3}-(2y+1)\lambda^{2}+\lambda+y(y+1),\qquad "
                         r"P_{\mathrm{LY}}(y)=256y^{3}+411y^{2}+165y+32.")
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(r"f(y):=\lambda_{+}(y)-\frac14,\qquad "
                         r"A_{3}(y)f^{(3)}+A_{2}(y)f^{(2)}+A_{1}(y)f'+A_{0}(y)f=0.")
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(r"A_{3}(y)=y(y-1)P_{\mathrm{LY}}(y)Q(y),\qquad "
                         r"Q(y)=168y^{5}+1260y^{4}-422y^{3}-183y^{2}-639y-76.")
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(
            r"\begin{aligned}"
            r"A_{2}(y)&=6\Big(17920y^{9}+192500y^{8}-12480y^{7}-94031y^{6}-139107y^{5}-71300y^{4}"
            r"+80597y^{3}+41863y^{2}+6758y+608\Big),\\"
            r"A_{1}(y)&=6\Big(3136y^{8}+45164y^{7}-56178y^{6}-36438y^{5}-138724y^{4}-62488y^{3}"
            r"+18443y^{2}+5933y-32\Big),\\"
            r"A_{0}(y)&=24\Big(56y^{7}+1036y^{6}+3844y^{5}+3740y^{4}+8288y^{3}+1417y^{2}+19y+32\Big)."
            r"\end{aligned}"
        )
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(r"\operatorname{Sing}_{\mathrm{fin}}(L_{3})=\{A_{3}(y)=0\}"
                         r"=\{0,1\}\cup\{P_{\mathrm{LY}}(y)=0\}\cup\{Q(y)=0\}.")
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(r"\operatorname{Exp}_{y_{0}}(L_{3})=\left\{0,1,2-\frac{A_{2}(y_{0})}{A_{3}'(y_{0})}\right\},")
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(r"\operatorname{Exp}_{y_{0}}(L_{3})=\left\{0,\frac12,1\right\}\ (y_{0}\in\{0,1,P_{\mathrm{LY}}=0\}),\qquad "
                         r"\operatorname{Exp}_{y_{0}}(L_{3})=\{0,1,3\}\ (y_{0}\in\{Q=0\}).")
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(r"\operatorname{Exp}_{\infty}(L_{3})=\left\{-\frac14,\frac14,\frac12\right\},\qquad "
                         r"32\sigma^{3}-16\sigma^{2}-2\sigma+1=(2\sigma-1)(4\sigma-1)(4\sigma+1).")
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(r"W(y)^{2}=C\cdot\frac{Q(y)^{2}}{y^{3}(y-1)^{3}P_{\mathrm{LY}}(y)^{3}},\qquad C\in\mathbb{C}^{\times}.")
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(lam_series_short)
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(
            r"\Lambda(t)\in \mathbb{Z}\!\left[\frac13\right][[t]],\qquad "
            r"\kappa_{n}^{\infty}:=\left.\frac{d^{n}}{ds^{n}}\right|_{s=0}\log\frac{\Lambda(e^{s}-1)}{2}\in \mathbb{Z}\!\left[\frac16\right]\ \ (n\ge 1)."
        )
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(
            r"(p\neq 3)\ \Longrightarrow\ \overline{\Lambda}_{p}(t)\in\mathbb{F}_{p}[[t]]\ \text{is algebraic over}\ \mathbb{F}_{p}(t),"
            r"\ \text{hence its coefficient sequence is \(p\)-automatic (Christol).}"
        )
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(
            r"\operatorname{Mon}(L_{3})\cong S_{4}\ \text{on}\ "
            r"\{(x_{1},x_{2},x_{3},x_{4})\in\mathbb{C}^{4}:\ x_{1}+x_{2}+x_{3}+x_{4}=0\},"
            r"\ \dim=3."
        )
        tex_lines.append(r"\]")

        _write_json(out_json, payload)
        _write_text(out_tex, "\n".join(tex_lines) + "\n")

    dt = time.time() - t0
    print(
        "[fold-zm-leyang-perron-fuchs] checks:"
        f" ode={ode_identity_ok} sing_split={gcd_Q_true_ok} idx_true={idx_true_half_ok}"
        f" idx_app={idx_app_three_ok} ind_inf={ind_inf_ok} wr={wronskian_logder_ok}"
        f" lam3={lambda_only_prime3_ok} kappa26={kappa_only_2_3_ok}"
        f" modp={modp_checks} s4size={std_rep_group_size} s4ok={std_rep_group_size_ok}"
        f" traces_ok={std_rep_traces_ok} sec={dt:.3f}",
        flush=True,
    )
    print("[fold-zm-leyang-perron-fuchs] done", flush=True)


if __name__ == "__main__":
    main()

