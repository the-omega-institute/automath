#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit closed-form thermodynamic formulas for the 4x4 collision input skeleton, and its 3-parameter Gibbs twist family.

We work on the golden-mean product shift X×X with adjacency
  A = F ⊗ F,  F = [[1,1],[1,0]],
on the 4 memory states {00,01,10,11} (in this fixed order).

For the collision potential (indicator of state 11), we use the 1-parameter diagonal twist:
  D(u) = diag(1,1,1,u),  u>0,
and the weighted transfer matrix in the same convention as the main text:
  W(u) = A D(u).

The paper states several closed forms in terms of the Perron root rho(W(u)):
  - inversion u = u(rho),
  - equilibrium one-site distribution pi_{00}, pi_{01}, pi_{10}, pi_{11} (rational in rho),
  - elimination cubic linking alpha=pi_{11} to rho,
and the 3-parameter family:
  D(a,b,c) = diag(1,b,a,abc),  a,b,c>0,
  W(a,b,c) = A D(a,b,c),
whose Perron root Λ satisfies a universal quartic characteristic equation.

This script numerically certifies these identities on a few sample parameter points.

Outputs:
  - artifacts/export/collision_input_4x4_gibbs_closed_form_audit.json
  - sections/generated/tab_collision_input_4x4_gibbs_closed_form_audit.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir


def _A() -> np.ndarray:
    # State order: 00, 01, 10, 11
    return np.array(
        [
            [1.0, 1.0, 1.0, 1.0],
            [1.0, 0.0, 1.0, 0.0],
            [1.0, 1.0, 0.0, 0.0],
            [1.0, 0.0, 0.0, 0.0],
        ],
        dtype=float,
    )


def _W_u(u: float) -> np.ndarray:
    D = np.diag([1.0, 1.0, 1.0, float(u)])
    return _A() @ D


def _W_abc(a: float, b: float, c: float) -> np.ndarray:
    D = np.diag([1.0, float(b), float(a), float(a) * float(b) * float(c)])
    return _A() @ D


def _perron_right(M: np.ndarray) -> Tuple[float, np.ndarray]:
    vals, vecs = np.linalg.eig(M)
    idx = int(np.argmax(np.real(vals)))
    lam = vals[idx]
    r = np.real(vecs[:, idx])
    # Fix sign deterministically (all-positive for primitive nonnegative matrices).
    if float(r[0]) < 0:
        r *= -1.0
    return float(np.real(lam)), r


def _perron_left(M: np.ndarray) -> Tuple[float, np.ndarray]:
    vals, vecs = np.linalg.eig(M.T)
    idx = int(np.argmax(np.real(vals)))
    lam = vals[idx]
    l = np.real(vecs[:, idx])
    if float(l[0]) < 0:
        l *= -1.0
    return float(np.real(lam)), l


def _stationary_pi(M: np.ndarray) -> Tuple[float, np.ndarray]:
    lam_r, r = _perron_right(M)
    lam_l, l = _perron_left(M)
    if abs(lam_r - lam_l) > 1e-8:
        raise RuntimeError(f"left/right Perron eigenvalues disagree: {lam_r} vs {lam_l}")
    # Normalize l^T r = 1.
    s = float(l @ r)
    if s == 0.0:
        raise RuntimeError("unexpected: l^T r = 0")
    l = l / s
    pi = (l * r).astype(float)
    pi = pi / float(np.sum(pi))
    return lam_r, pi


def _D_rho(rho: float) -> float:
    return 2.0 * rho**3 - 5.0 * rho**2 + 4.0 * rho + 1.0


def _u_from_rho(rho: float) -> float:
    return (rho * (rho**2 - 2.0 * rho - 1.0)) / (rho - 1.0)


def _alpha_from_rho(rho: float) -> float:
    return (rho**3 - 3.0 * rho**2 + rho + 1.0) / _D_rho(rho)


def _pi_closed_from_rho(rho: float) -> np.ndarray:
    D = _D_rho(rho)
    pi00 = rho * (rho - 1.0) ** 2 / D
    pi01 = rho / D
    pi10 = rho / D
    pi11 = (rho**3 - 3.0 * rho**2 + rho + 1.0) / D
    return np.array([pi00, pi01, pi10, pi11], dtype=float)


def _elim_cubic_residual(alpha: float, rho: float) -> float:
    # (2α-1)ρ^3+(3-5α)ρ^2+(4α-1)ρ+(α-1)=0
    return (2.0 * alpha - 1.0) * rho**3 + (3.0 - 5.0 * alpha) * rho**2 + (4.0 * alpha - 1.0) * rho + (alpha - 1.0)


def _quartic_residual(L: float, a: float, b: float, c: float) -> float:
    # L^4 - L^3 - (a+b+ab+abc)L^2 - ab L + a^2 b^2 c = 0
    return L**4 - L**3 - (a + b + a * b + a * b * c) * L**2 - (a * b) * L + (a * a * b * b * c)


@dataclass(frozen=True)
class CollisionRow:
    u: float
    rho: float
    pi_err_max_abs: float
    u_inv_rel_err: float
    elim_cubic_abs: float


@dataclass(frozen=True)
class ThreeParamRow:
    a: float
    b: float
    c: float
    Lambda: float
    quartic_abs: float


def _fmt_float(x: float, *, ndigits: int = 12) -> str:
    return f"{x:.{ndigits}f}"


def _fmt_sci(x: float) -> str:
    return f"{x:.2e}"


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit collision 4x4 closed forms and the 3-parameter quartic family.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_input_4x4_gibbs_closed_form_audit.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-tab-out",
        type=str,
        default=str(generated_dir() / "tab_collision_input_4x4_gibbs_closed_form_audit.tex"),
        help="Output LaTeX table snippet path.",
    )
    args = parser.parse_args()

    u_list = [0.05, 0.2, 0.7, 1.0, 2.0, 10.0]
    abc_list = [(1.3, 0.8, 2.1), (2.0, 1.5, 0.4), (1.0, 1.0, 3.0), (0.7, 1.8, 1.2)]

    collision_rows: List[CollisionRow] = []
    for u in u_list:
        rho, pi_num = _stationary_pi(_W_u(u))
        pi_closed = _pi_closed_from_rho(rho)
        pi_err = float(np.max(np.abs(pi_num - pi_closed)))
        u_back = _u_from_rho(rho)
        u_rel = abs(float(u_back - u)) / float(u)
        alpha = _alpha_from_rho(rho)
        elim_abs = abs(float(_elim_cubic_residual(alpha, rho)))
        collision_rows.append(
            CollisionRow(u=float(u), rho=float(rho), pi_err_max_abs=pi_err, u_inv_rel_err=u_rel, elim_cubic_abs=elim_abs)
        )

    three_rows: List[ThreeParamRow] = []
    for a, b, c in abc_list:
        L, _pi = _stationary_pi(_W_abc(a, b, c))
        q_abs = abs(float(_quartic_residual(L, a, b, c)))
        three_rows.append(ThreeParamRow(a=float(a), b=float(b), c=float(c), Lambda=float(L), quartic_abs=q_abs))

    # Write JSON
    out_json = Path(args.json_out)
    out_json.parent.mkdir(parents=True, exist_ok=True)
    payload: Dict[str, object] = {
        "u_samples": [asdict(r) for r in collision_rows],
        "abc_samples": [asdict(r) for r in three_rows],
    }
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Write LaTeX table
    out_tex = Path(args.tex_tab_out)
    out_tex.parent.mkdir(parents=True, exist_ok=True)

    lines: List[str] = []
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\scriptsize")
    lines.append(r"\setlength{\tabcolsep}{6pt}")
    lines.append(
        r"\caption{Audit for the $4\times4$ collision input skeleton closed forms and the $3$-parameter Gibbs twist quartic. "
        r"We report the max absolute error between the numerical PF equilibrium one-site law and the rational closed form, "
        r"the relative inversion error for $u(\rho)$, the absolute residual of the $(\alpha,\rho)$ elimination cubic, "
        r"and the absolute residual of the universal quartic at the numerical Perron root.}"
    )
    lines.append(r"\label{tab:collision_input_4x4_gibbs_closed_form_audit}")
    lines.append(r"\begin{tabular}{l r r r r r}")
    lines.append(r"\toprule")
    lines.append(r"case & root & $\max|\pi-\pi_{\mathrm{cf}}|$ & rel err $u(\rho)$ & $|R_{\alpha,\rho}|$ & $|Q_4|$\\")
    lines.append(r"\midrule")
    for r in collision_rows:
        lines.append(
            f"collision: $u={r.u:g}$ & {_fmt_float(r.rho)} & {_fmt_sci(r.pi_err_max_abs)} & {_fmt_sci(r.u_inv_rel_err)} & {_fmt_sci(r.elim_cubic_abs)} & --\\\\"
        )
    lines.append(r"\midrule")
    for r in three_rows:
        lines.append(
            f"3-param: $(a,b,c)=({r.a:g},{r.b:g},{r.c:g})$ & {_fmt_float(r.Lambda)} & -- & -- & -- & {_fmt_sci(r.quartic_abs)}\\\\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    out_tex.write_text("\n".join(lines) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

