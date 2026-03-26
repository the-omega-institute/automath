#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the "diagonal observation completeness" for the optimal diagonal-rate kernel K*_delta.

This script is English-only by repository convention.

We verify (numerically, high precision) that the diagonal keep-rate vector
  p_delta(x) := K*_delta(x|x)
uniquely determines:
  - kappa via   sum_x p / (1 + kappa - kappa p) = 1,
  - the refresh/background distribution pi,
  - delta via   delta = (1 - s2) / (1 + kappa s2),  s2 = sum_x pi(x)^2,
  - w via        w(x) ∝ p / (1 + kappa - kappa p)^2,
  - the full kernel K* via the diagonal-closure rank-one formula,
  - the determinant identity:
        det(I - z K*) = Ptilde(kappa z) + z Ptilde'(kappa z),
    where Ptilde(z)=∏_x (1 - (p(x)/(1+kappa)) z).

Outputs:
  - artifacts/export/pom_diagonal_rate_diagonal_observation_audit.json
  - sections/generated/eq_pom_diagonal_rate_diagonal_observation_audit.tex
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import mpmath as mp

from common_diagonal_rate import ScalarCollapseSolution, delta0_from_w, solve_scalar_collapse
from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _bisect_root(f, lo: mp.mpf, hi: mp.mpf, *, tol: mp.mpf, max_iter: int) -> mp.mpf:
    flo = f(lo)
    fhi = f(hi)
    if flo == 0:
        return lo
    if fhi == 0:
        return hi
    if flo * fhi > 0:
        raise RuntimeError("Root is not bracketed.")
    for _ in range(max_iter):
        mid = (lo + hi) / 2
        fmid = f(mid)
        if abs(fmid) <= tol:
            return mid
        if flo * fmid < 0:
            hi, fhi = mid, fmid
        else:
            lo, flo = mid, fmid
        if abs(hi - lo) <= tol * (mp.mpf(1) + abs(mid)):
            break
    return (lo + hi) / 2


def _build_kernel_from_scalar_collapse(w: List[mp.mpf], sol: ScalarCollapseSolution) -> List[List[mp.mpf]]:
    n = len(w)
    kappa = sol.kappa
    Z = sol.Z
    u = sol.u
    K: List[List[mp.mpf]] = [[mp.mpf(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            Pij = (u[i] * u[j]) / Z
            if i == j:
                Pij = (mp.mpf(1) + kappa) * (u[i] * u[i]) / Z
            K[i][j] = Pij / w[i]
    return K


def _diag_of(K: List[List[mp.mpf]]) -> List[mp.mpf]:
    return [K[i][i] for i in range(len(K))]


def _reconstruct_kappa_from_diag(p: Sequence[mp.mpf], *, tol: mp.mpf, max_iter: int) -> mp.mpf:
    def F(kappa: mp.mpf) -> mp.mpf:
        s = mp.mpf(0)
        for px in p:
            s += px / (mp.mpf(1) + kappa - kappa * px)
        return s - mp.mpf(1)

    lo = mp.mpf(0)
    hi = mp.mpf(1)
    # F(lo) should be >0 in the non-degenerate regime; bracket anyway.
    while F(hi) > 0:
        hi *= 2
        if hi > mp.mpf("1e12"):
            raise RuntimeError("Failed to bracket kappa from diagonal equation.")
    return _bisect_root(F, lo, hi, tol=tol, max_iter=max_iter)


def _reconstruct_pi_from_diag(p: Sequence[mp.mpf], kappa: mp.mpf) -> List[mp.mpf]:
    return [px / (mp.mpf(1) + kappa - kappa * px) for px in p]


def _reconstruct_delta_from_pi(pi: Sequence[mp.mpf], kappa: mp.mpf) -> mp.mpf:
    s2 = mp.fsum([q * q for q in pi])
    return (mp.mpf(1) - s2) / (mp.mpf(1) + kappa * s2)


def _reconstruct_w_from_diag(p: Sequence[mp.mpf], kappa: mp.mpf) -> List[mp.mpf]:
    nums = [px / (mp.mpf(1) + kappa - kappa * px) ** 2 for px in p]
    Z = mp.fsum(nums)
    return [x / Z for x in nums]


def _reconstruct_K_from_diag(p: Sequence[mp.mpf], kappa: mp.mpf) -> List[List[mp.mpf]]:
    n = len(p)
    pi = _reconstruct_pi_from_diag(p, kappa)
    K: List[List[mp.mpf]] = [[mp.mpf(0) for _ in range(n)] for _ in range(n)]
    factor = kappa / (mp.mpf(1) + kappa)
    for i in range(n):
        for j in range(n):
            if i == j:
                K[i][j] = p[i]
            else:
                K[i][j] = (mp.mpf(1) - factor * p[i]) * pi[j]
    return K


def _max_abs_diff(A: Sequence[Sequence[mp.mpf]], B: Sequence[Sequence[mp.mpf]]) -> mp.mpf:
    n = len(A)
    m = len(A[0])
    out = mp.mpf(0)
    for i in range(n):
        for j in range(m):
            out = max(out, abs(A[i][j] - B[i][j]))
    return out


def _poly_Ptilde(p: Sequence[mp.mpf], kappa: mp.mpf, z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    out = mp.mpf(1)
    denom = mp.mpf(1) + kappa
    for px in p:
        out *= mp.mpf(1) - (px / denom) * z
    return out


def _poly_Ptilde_prime(p: Sequence[mp.mpf], kappa: mp.mpf, z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    P = _poly_Ptilde(p, kappa, z)
    denom = mp.mpf(1) + kappa
    s = mp.mpf(0)
    for px in p:
        a = px / denom
        s += a / (mp.mpf(1) - a * z)
    return -P * s


def _det_I_minus_zK(K: List[List[mp.mpf]], z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
    n = len(K)
    M = mp.matrix(n)
    for i in range(n):
        for j in range(n):
            M[i, j] = (mp.mpf(1) if i == j else mp.mpf(0)) - z * K[i][j]
    return mp.det(M)


@dataclass(frozen=True)
class CaseRow:
    delta_in: str
    delta0: str
    kappa_true: str
    kappa_rec: str
    delta_true: str
    delta_rec: str
    sum_p: str
    sum_pi: str
    max_abs_err_w: str
    max_abs_err_K: str
    det_rel_err_real: str
    det_rel_err_complex: str


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit diagonal observation completeness for K*_delta.")
    parser.add_argument("--dps", type=int, default=90, help="Decimal precision (default: 90).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    dps = int(args.dps)
    if dps < 60:
        raise SystemExit("Require --dps >= 60 for stable outputs.")
    mp.mp.dps = dps

    tol = mp.mpf(10) ** (-(mp.mp.dps // 2))

    # Example full-support distribution (same as scalar-collapse audit).
    w = [mp.mpf("0.37"), mp.mpf("0.21"), mp.mpf("0.17"), mp.mpf("0.13"), mp.mpf("0.12")]
    d0 = delta0_from_w(w)

    # Representative deltas (non-degenerate).
    deltas = [mp.mpf("0.02"), mp.mpf("0.10"), mp.mpf("0.25")]
    rows: List[CaseRow] = []

    for delta_in in deltas:
        sol = solve_scalar_collapse(w, delta_in, dps=dps)
        K_true = _build_kernel_from_scalar_collapse(w, sol)
        p = _diag_of(K_true)

        k_rec = _reconstruct_kappa_from_diag(p, tol=tol, max_iter=400)
        pi_rec = _reconstruct_pi_from_diag(p, k_rec)
        delta_rec = _reconstruct_delta_from_pi(pi_rec, k_rec)
        w_rec = _reconstruct_w_from_diag(p, k_rec)
        K_rec = _reconstruct_K_from_diag(p, k_rec)

        # Errors.
        max_w_err = max(abs(a - b) for a, b in zip(w, w_rec))
        max_K_err = _max_abs_diff(K_true, K_rec)

        # Determinant identity checks.
        z_real = mp.mpf("0.37")
        z_cplx = mp.mpc("0.21", "0.13")
        det_left_r = _det_I_minus_zK(K_true, z_real)
        det_right_r = _poly_Ptilde(p, k_rec, k_rec * z_real) + z_real * _poly_Ptilde_prime(p, k_rec, k_rec * z_real)
        det_left_c = _det_I_minus_zK(K_true, z_cplx)
        det_right_c = _poly_Ptilde(p, k_rec, k_rec * z_cplx) + z_cplx * _poly_Ptilde_prime(p, k_rec, k_rec * z_cplx)

        def rel_err(a, b) -> mp.mpf:
            denom = max(mp.mpf(1), abs(a), abs(b))
            return abs(a - b) / denom

        det_err_r = rel_err(det_left_r, det_right_r)
        det_err_c = rel_err(det_left_c, det_right_c)

        rows.append(
            CaseRow(
                delta_in=mp.nstr(delta_in, 25),
                delta0=mp.nstr(d0, 25),
                kappa_true=mp.nstr(sol.kappa, 25),
                kappa_rec=mp.nstr(k_rec, 25),
                delta_true=mp.nstr(sol.delta, 25),
                delta_rec=mp.nstr(delta_rec, 25),
                sum_p=mp.nstr(mp.fsum(p), 25),
                sum_pi=mp.nstr(mp.fsum(pi_rec), 25),
                max_abs_err_w=mp.nstr(max_w_err, 10),
                max_abs_err_K=mp.nstr(max_K_err, 10),
                det_rel_err_real=mp.nstr(det_err_r, 10),
                det_rel_err_complex=mp.nstr(det_err_c, 10),
            )
        )

    payload: Dict[str, object] = {
        "w": [mp.nstr(x, 25) for x in w],
        "delta0": mp.nstr(d0, 25),
        "cases": [asdict(r) for r in rows],
    }

    if not args.no_output:
        out_json = export_dir() / "pom_diagonal_rate_diagonal_observation_audit.json"
        _write_json(out_json, payload)

        # TeX snippet (formulas + one numeric instantiation).
        ex = rows[0]
        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_pom_diagonal_rate_diagonal_observation_audit.py",
                "\\[",
                "\\sum_x \\frac{p(x)}{1+\\kappa-\\kappa p(x)}=1,\\qquad"
                "\\pi(x)=\\frac{p(x)}{1+\\kappa-\\kappa p(x)},\\qquad "
                "w(x)\\propto \\frac{p(x)}{(1+\\kappa-\\kappa p(x))^{2}}.",
                "\\]",
                "\\[",
                "\\det(I-zK^\\star_\\delta)"
                "=\\widetilde{\\mathcal P}_\\delta(\\kappa z)+z\\,\\widetilde{\\mathcal P}_\\delta'(\\kappa z),\\qquad"
                "\\widetilde{\\mathcal P}_\\delta(z)=\\prod_x\\left(1-\\frac{p(x)}{1+\\kappa}z\\right).",
                "\\]",
                "\\[",
                f"\\text{{Example: }}\\delta={ex.delta_in},\\ "
                f"\\kappa\\approx {ex.kappa_rec},\\ "
                f"\\max|w-w_{{\\rm rec}}|\\approx {ex.max_abs_err_w},\\ "
                f"\\max|K-K_{{\\rm rec}}|\\approx {ex.max_abs_err_K}.",
                "\\]",
                "",
            ]
        )
        out_tex = generated_dir() / "eq_pom_diagonal_rate_diagonal_observation_audit.tex"
        _write_text(out_tex, tex)

        print(f"[pom-diagonal-rate-diagonal-observation] wrote {out_json}", flush=True)
        print(f"[pom-diagonal-rate-diagonal-observation] wrote {out_tex}", flush=True)


if __name__ == "__main__":
    main()

