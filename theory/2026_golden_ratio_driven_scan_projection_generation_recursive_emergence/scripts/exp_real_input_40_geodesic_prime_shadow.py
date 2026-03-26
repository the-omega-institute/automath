#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Geodesic (non-backtracking) prime shadow for the real-input 40-state kernel.

We work on the essential 20-state core and its directed edge set E (|E|=48),
build the edge-edge transition family H(t) with a backtracking fugacity t,
and export:

- the non-backtracking determinant det(I - z H(0)),
- the non-backtracking roots z_j of det(I - z H(0)) and the strict Ramanujan margin,
- the first primitive counts p_n^{nb},
- the geodesic Mertens constant (Abel finite part),
- the Bartholdi-type 2-variable determinant factorization
    det(I - z H(t)) = (1 - t^2 z^2) (1 + t(1-t) z^2)^2 F(z,t),
  with F(z,t)=sum_{k=0}^{20} f_k(t) z^k, f_k in Z[t],
- the closed forms for P'(0), P''(0) where P(theta)=log rho(H(e^theta)).

Outputs (default):
- artifacts/export/real_input_40_geodesic_prime_shadow.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
import sympy as sp

from common_paths import export_dir
from common_phi_fold import Progress
from exp_real_input_40_rotation_polytope_exact import _build_graph_40, _extract_essential_scc


@dataclass(frozen=True)
class EdgePairMatrices:
    H_nb: List[List[int]]  # non-backtracking transitions (weight 1)
    B_bt: List[List[int]]  # backtracking transitions (weight 1; scaled by t in H(t))


def _mobius(n: int) -> int:
    if n == 1:
        return 1
    mu = 1
    p = 2
    nn = n
    while p * p <= nn:
        if nn % p == 0:
            nn //= p
            if nn % p == 0:
                return 0
            mu = -mu
        p += 1
    if nn > 1:
        mu = -mu
    return mu


def _build_edge_pair_matrices(edges_ess) -> EdgePairMatrices:
    E = len(edges_ess)
    H_nb = [[0] * E for _ in range(E)]
    B_bt = [[0] * E for _ in range(E)]
    for i, e1 in enumerate(edges_ess):
        u, v = int(e1.src), int(e1.dst)
        for j, e2 in enumerate(edges_ess):
            if int(e2.src) != v:
                continue
            w = int(e2.dst)
            if w == u:
                B_bt[i][j] = 1
            else:
                H_nb[i][j] = 1
    return EdgePairMatrices(H_nb=H_nb, B_bt=B_bt)


def _det_I_minus_zM_poly(M: sp.Matrix, z: sp.Symbol) -> sp.Poly:
    """
    For an integer matrix M (n x n), compute det(I - z M) as a polynomial in z over ZZ.

    Using charpoly: cp(lam)=det(lam I - M)=lam^n + a1 lam^{n-1}+...+an.
    Then det(I - zM)=z^n cp(1/z)=1 + a1 z + ... + an z^n.
    """
    lam = sp.Symbol("lam")
    cp = M.charpoly(lam)
    coeffs = cp.all_coeffs()  # [1, a1, ..., an]
    expr = sum(sp.Integer(coeffs[i]) * z**i for i in range(len(coeffs)))
    return sp.Poly(expr, z, domain=sp.ZZ)


def _traces_and_primitives(H_nb: np.ndarray, max_n: int, prog: Progress) -> Tuple[List[int], List[int]]:
    A = H_nb.copy()
    traces: List[int] = []
    for n in range(1, max_n + 1):
        if n > 1:
            A = A.dot(H_nb)
        traces.append(int(np.trace(A)))
        prog.tick(f"geodesic trace n={n}/{max_n}")

    pvals: List[int] = []
    for n in range(1, max_n + 1):
        s = 0
        for d in range(1, n + 1):
            if n % d == 0:
                s += _mobius(d) * traces[n // d - 1]
        if s % n != 0:
            raise ValueError(f"p_n not integer at n={n}")
        pvals.append(s // n)
    return traces, pvals


def _decimal_poly_eval(coeffs_low_to_high: List[int], z: Decimal) -> Decimal:
    # Horner evaluation from highest degree
    acc = Decimal(0)
    for a in reversed(coeffs_low_to_high):
        acc = acc * z + Decimal(a)
    return acc


def _decimal_poly_derivative_eval(coeffs_low_to_high: List[int], z: Decimal) -> Decimal:
    # Evaluate derivative of sum a_k z^k
    acc = Decimal(0)
    powz = Decimal(1)
    for k, a in enumerate(coeffs_low_to_high[1:], start=1):
        acc += Decimal(k) * Decimal(a) * powz
        powz *= z
    return acc


def main() -> None:
    parser = argparse.ArgumentParser(description="Geodesic prime shadow for real-input-40 kernel (edge-space)")
    parser.add_argument("--max-n", type=int, default=15, help="Max n for a_n/p_n outputs")
    parser.add_argument("--mertens-m-max", type=int, default=200, help="Max m for zeta-based Abel finite part series")
    parser.add_argument("--precision", type=int, default=90, help="Decimal precision")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output")
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/real_input_40_geodesic_prime_shadow.json)",
    )
    args = parser.parse_args()

    prog = Progress(label="real-input-40-geodesic-prime-shadow", every_seconds=20.0)

    # Build essential core graph and its directed edges (48)
    states40, edges40 = _build_graph_40()
    ess_nodes, edges_ess = _extract_essential_scc(states40, edges40)
    V = len(ess_nodes)
    E = len(edges_ess)
    if V != 20 or E != 48:
        raise SystemExit(f"expected (V,E)=(20,48), got (V,E)=({V},{E})")

    mats = _build_edge_pair_matrices(edges_ess)
    H_nb_np = np.array(mats.H_nb, dtype=np.int64)

    # det(I - z H_nb)
    z = sp.Symbol("z")
    det_nb_poly = _det_I_minus_zM_poly(sp.Matrix(mats.H_nb), z)
    det_nb_coeffs = [int(det_nb_poly.nth(k)) for k in range(det_nb_poly.degree() + 1)]

    # Nonzero characteristic polynomial (degree 15) in rho
    rho = sp.Symbol("rho")
    char_nb = sp.expand(rho ** det_nb_poly.degree() * det_nb_poly.as_expr().subs(z, 1 / rho))

    # Largest real root (Perron) for rho_nb
    rho_roots = sp.nroots(char_nb, n=50, maxsteps=200)
    rho_real = sorted([sp.re(r) for r in rho_roots if abs(sp.im(r)) < sp.Float("1e-40")])[-1]
    rho_nb = sp.N(rho_real, 50)

    # Roots of det(I - z H_nb) and strict Ramanujan margin
    z_roots = sp.nroots(det_nb_poly.as_expr(), n=80, maxsteps=200)
    z_star_sym = sp.N(1 / rho_nb, 80)

    def _cabs80(x: sp.Expr) -> float:
        return abs(complex(sp.N(x, 80)))

    # Identify the Perron reciprocal root via proximity to z_star
    z_root1 = min(z_roots, key=lambda r: _cabs80(r - z_star_sym))
    # Second-smallest modulus root (excluding z_root1 instance)
    z_roots_sorted = sorted(z_roots, key=_cabs80)
    z1_idx = min(range(len(z_roots_sorted)), key=lambda i: _cabs80(z_roots_sorted[i] - z_root1))
    z_roots_wo_z1 = z_roots_sorted[:z1_idx] + z_roots_sorted[z1_idx + 1 :]
    z_root2 = z_roots_wo_z1[0]

    abs_z1 = sp.N(sp.Abs(z_root1), 50)
    abs_z2 = sp.N(sp.Abs(z_root2), 50)
    Lambda_nb = sp.N(1 / abs_z2, 50)
    ratio_nb = sp.N(Lambda_nb / sp.sqrt(rho_nb), 50)
    delta_nb = sp.N(sp.log(Lambda_nb**2 / rho_nb), 50)

    # Primitive counts
    a_n, p_n = _traces_and_primitives(H_nb=H_nb_np, max_n=args.max_n, prog=prog)

    # Mertens / Abel finite part constant for geodesic primes
    getcontext().prec = args.precision
    rho_dec = Decimal(str(rho_nb))
    z_star = Decimal(1) / rho_dec

    # residue constant C = lim_{z->z*} (1 - rho z) zeta(z) = -rho / Delta'(z*)
    Dp = _decimal_poly_derivative_eval(det_nb_coeffs, z_star)
    C = -(rho_dec) / Dp

    def zeta_dec(zz: Decimal) -> Decimal:
        return Decimal(1) / _decimal_poly_eval(det_nb_coeffs, zz)

    s = Decimal(0)
    for m in range(2, args.mertens_m_max + 1):
        mu = _mobius(m)
        if mu == 0:
            continue
        s += (Decimal(mu) / Decimal(m)) * zeta_dec(z_star**m).ln()
        if m % 25 == 0:
            prog.tick(f"mertens series m={m}/{args.mertens_m_max}")

    log_mathfrak_M = C.ln() + s
    mathfrak_M = log_mathfrak_M.exp()
    gamma_dec = Decimal("0.577215664901532860606512090082402431")
    mertens_star = gamma_dec + log_mathfrak_M

    # Bartholdi factorization coefficients f_k(t) by interpolation in t
    t = sp.Symbol("t")
    max_k = 20
    T = list(range(0, 21))
    vals: Dict[int, List[int]] = {k: [] for k in range(max_k + 1)}

    for tv in T:
        Ht = [[mats.H_nb[i][j] + tv * mats.B_bt[i][j] for j in range(E)] for i in range(E)]
        M = sp.Matrix(Ht)
        Delta_tv = _det_I_minus_zM_poly(M, z)
        fac = (1 - (tv**2) * z**2) * (1 + tv * (1 - tv) * z**2) ** 2
        Q, R = sp.div(Delta_tv.as_expr(), fac, domain=sp.ZZ)
        if sp.simplify(R) != 0:
            raise SystemExit(f"factorization remainder nonzero at t={tv}: {R}")
        F_tv = sp.Poly(Q, z, domain=sp.ZZ)
        for k in range(max_k + 1):
            vals[k].append(int(F_tv.nth(k)))

    f_polys: Dict[int, sp.Poly] = {}
    for k in range(max_k + 1):
        points = [(sp.Integer(tv), sp.Integer(v)) for tv, v in zip(T, vals[k])]
        fk = sp.interpolate(points, t)
        pk = sp.Poly(sp.expand(fk), t, domain=sp.QQ)
        if any(c.q != 1 for c in pk.all_coeffs()):
            raise SystemExit(f"non-integer coeffs in f_{k}(t): {pk}")
        f_polys[k] = sp.Poly(pk.as_expr(), t, domain=sp.ZZ)

    # Exact P'(0), P''(0) from implicit derivatives at (z0,t0)=(phi^{-2},1)
    sqrt5 = sp.sqrt(5)
    phi2 = (sp.Integer(3) + sqrt5) / 2
    z0 = 1 / phi2
    t0 = sp.Integer(1)

    F_sym = sum(f_polys[k].as_expr().subs(t, t) * z**k for k in range(max_k + 1))
    Delta_sym = (1 - t**2 * z**2) * (1 + t * (1 - t) * z**2) ** 2 * F_sym
    Dz = sp.diff(Delta_sym, z)
    Dt = sp.diff(Delta_sym, t)
    Dzz = sp.diff(Dz, z)
    Dzt = sp.diff(Dz, t)
    Dtt = sp.diff(Dt, t)

    subs = {z: z0, t: t0}
    Dz0 = sp.simplify(Dz.subs(subs))
    Dt0 = sp.simplify(Dt.subs(subs))
    Dzz0 = sp.simplify(Dzz.subs(subs))
    Dzt0 = sp.simplify(Dzt.subs(subs))
    Dtt0 = sp.simplify(Dtt.subs(subs))

    z_t = sp.simplify(-Dt0 / Dz0)
    z_tt = sp.simplify(-(Dzz0 * z_t**2 + 2 * Dzt0 * z_t + Dtt0) / Dz0)
    # theta derivatives: t=e^theta => z'(0)=z_t, z''(0)=z_tt+z_t
    z1 = z_t
    z2 = sp.simplify(z_tt + z_t)
    P1 = sp.simplify(-z1 / z0)
    P2 = sp.simplify(-z2 / z0 + (z1 / z0) ** 2)

    payload: Dict[str, object] = {
        "core_sizes": {"V": V, "E": E},
        "det_nb": {
            "poly_str": str(det_nb_poly.as_expr()),
            "degree_z": int(det_nb_poly.degree()),
            "coeffs_low_to_high": det_nb_coeffs,
        },
        "det_nb_roots": {
            "z_star": str(sp.N(z_star_sym, 50)),
            "roots_sorted_by_abs": [str(sp.N(r, 50)) for r in z_roots_sorted],
            "z1": str(sp.N(z_root1, 50)),
            "z2": str(sp.N(z_root2, 50)),
            "abs_z1": str(abs_z1),
            "abs_z2": str(abs_z2),
            "Lambda_nb": str(Lambda_nb),
            "Lambda_over_sqrt_rho_nb": str(ratio_nb),
            "delta_nb": str(delta_nb),
        },
        "char_nb_rho": {"poly_str": str(char_nb)},
        "rho_nb": str(rho_nb),
        "h_nb": str(sp.N(sp.log(rho_real), 50)),
        "a_n_nb": a_n,
        "p_n_nb": p_n,
        "geodesic_mertens": {
            "z_star": str(z_star),
            "residue_C": str(C),
            "log_mathfrak_M": str(log_mathfrak_M),
            "mathfrak_M": str(mathfrak_M),
            "mertens_star": str(mertens_star),
            "mertens_m_max": args.mertens_m_max,
        },
        "bartholdi_factorization": {
            "Delta_factor": "(1-t^2 z^2) (1+t(1-t) z^2)^2 F(z,t)",
            "F_degree_z": 20,
            "f_k": {str(k): str(sp.factor(f_polys[k].as_expr())) for k in range(max_k + 1)},
        },
        "backtracking_cumulants_closed": {
            "z0": str(sp.simplify(z0)),
            "P1_exact": str(P1),
            "P2_exact": str(P2),
            "P1_numeric": str(sp.N(P1, 40)),
            "P2_numeric": str(sp.N(P2, 40)),
        },
    }

    if not args.no_output:
        out_path = Path(args.output) if args.output else export_dir() / "real_input_40_geodesic_prime_shadow.json"
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"[real-input-40-geodesic-prime-shadow] wrote {out_path}", flush=True)

    print(f"[real-input-40-geodesic-prime-shadow] V={V} E={E}", flush=True)
    print(f"[real-input-40-geodesic-prime-shadow] rho_nb={rho_nb}", flush=True)
    print(f"[real-input-40-geodesic-prime-shadow] logM_nb={log_mathfrak_M}", flush=True)
    print(f"[real-input-40-geodesic-prime-shadow] P'(0)={P1}  P''(0)={P2}", flush=True)
    print("[real-input-40-geodesic-prime-shadow] done", flush=True)


if __name__ == "__main__":
    main()

