#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Zero-temperature (u->infty) reduction for the real-input 40-state kernel, output potential only.

We start from the explicit factorization:
  Delta(z,u) = det(I - z M(u)) = (1 - u z^2) * F(z,u),
where F(z,u) is a degree-8 polynomial (see appendix tex).

We introduce the scaling:
  w := u z^2,  z = sqrt(w/u),
and take u -> +infty with w fixed. Odd powers in z contribute O(u^{-1/2}),
so the leading term is a quartic polynomial in w:
  F(sqrt(w/u),u) = Fhat(w) + O(u^{-1/2}),
  Fhat(w) = 1 - 6 w + 9 w^2 - w^3 - w^4.

We further exhibit a 4x4 nonnegative integer matrix B_inf with:
  det(I - w B_inf) = Fhat(w),
and compute its Perron root rho(B_inf), the associated Parry measure and
Markov transition matrix.

Outputs:
  - artifacts/export/real_input_40_output_potential_zero_temp_ground_sft.json
  - sections/generated/eq_real_input_40_output_potential_zero_temp_ground_sft.tex
"""

from __future__ import annotations

import argparse
import json
import threading
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np
import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class ZeroTempGroundSFT:
    # Fhat(w) coefficients, lowest to highest: sum_{k=0}^4 a_k w^k
    fhat_coeffs: List[int]
    # B_inf matrix (4x4)
    B_inf: List[List[int]]
    # Perron eigenvalue rho(B_inf)
    rho: float
    # b = 1/rho, c = sqrt(rho)
    b: float
    c: float
    # stationary distribution and transition matrix of the Parry Markov chain
    pi: List[float]
    P: List[List[float]]


class _Progress:
    def __init__(
        self, *, enabled: bool, every_seconds: float, prefix: str = "[zero-temp-ground]"
    ) -> None:
        self._enabled = enabled and every_seconds > 0
        self._every_seconds = float(every_seconds)
        self._prefix = prefix
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None
        self._t0 = 0.0

    def start(self, msg: str) -> None:
        if not self._enabled:
            return
        self._t0 = time.time()
        print(f"{self._prefix} {msg}", flush=True)

        def _run() -> None:
            while not self._stop.wait(self._every_seconds):
                dt = time.time() - self._t0
                print(f"{self._prefix} still running... elapsed={dt:.1f}s", flush=True)

        self._thread = threading.Thread(target=_run, name="progress", daemon=True)
        self._thread.start()

    def stop(self, msg: str) -> None:
        if not self._enabled:
            return
        self._stop.set()
        if self._thread is not None:
            self._thread.join(timeout=1.0)
        dt = time.time() - self._t0
        print(f"{self._prefix} {msg} elapsed={dt:.1f}s", flush=True)


def _build_F(z: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    # Must match `sections/appendix/sync_kernel/real_input/app__real-input-40-zeta-u.tex`.
    return (
        sp.Integer(1)
        - z
        - 6 * u * z**2
        + 2 * u * z**3
        + (9 * u**2 - u) * z**4
        + (u - 3 * u**2) * z**5
        - (u**3 + 2 * u**2) * z**6
        + (4 * u**3 - 3 * u**2) * z**7
        + (u**3 - u**4) * z**8
    )


def _leading_scaled_polynomial() -> Tuple[sp.Expr, List[int]]:
    """
    Compute Fhat(w) as the u->infty, w fixed leading term of F(sqrt(w/u),u).

    Implementation detail: F is a polynomial in z with coefficients polynomial in u.
    For each term c(u) z^n, under z = sqrt(w/u), we get:
      c(u) * w^{n/2} * u^{-n/2}.
    The leading contribution is O(1) iff deg_u(c) = n/2 and n is even.
    """
    z, u, w = sp.Symbol("z"), sp.Symbol("u"), sp.Symbol("w")
    F = sp.expand(_build_F(z, u))
    poly_z = sp.Poly(F, z)
    fhat = sp.Integer(0)
    for n, c_u in poly_z.terms():
        (nz,) = n
        if nz % 2 == 1:
            continue
        k = nz // 2
        cpoly = sp.Poly(sp.expand(c_u), u)
        if cpoly.is_zero:
            continue
        deg = int(cpoly.degree())
        if deg != k:
            continue
        lc = sp.Integer(cpoly.LC())
        fhat += lc * w**k
    fhat = sp.expand(fhat)
    coeffs = [int(sp.Poly(fhat, w).coeff_monomial(w**k)) for k in range(5)]
    return fhat, coeffs


def _parry_chain_from_adjacency(B: np.ndarray) -> Tuple[float, np.ndarray, np.ndarray]:
    """
    Return (rho, pi, P) for the Parry Markov chain of a nonnegative irreducible adjacency.
    """
    vals, vecs = np.linalg.eig(B.astype(float))
    i = int(np.argmax(np.abs(vals)))
    rho = float(np.real(vals[i]))
    v = np.real(vecs[:, i])
    if float(v.sum()) < 0:
        v = -v
    # Left eigenvector
    valsL, vecsL = np.linalg.eig(B.T.astype(float))
    j = int(np.argmax(np.abs(valsL)))
    ell = np.real(vecsL[:, j])
    if float(ell.sum()) < 0:
        ell = -ell
    # Normalize so that ell^T v = 1.
    ell = ell / float(ell @ v)
    pi = ell * v
    pi = pi / float(pi.sum())
    P = np.zeros_like(B, dtype=float)
    for a in range(B.shape[0]):
        for b in range(B.shape[1]):
            if B[a, b] != 0:
                P[a, b] = float(B[a, b]) * float(v[b]) / (rho * float(v[a]))
    return rho, pi, P


def _fmt_float(x: float, nd: int = 12) -> str:
    return f"{x:.{nd}f}"


def _write_tex(path: Path, res: ZeroTempGroundSFT) -> None:
    B = res.B_inf
    # Pretty-print Fhat(w) in increasing powers for readability.
    # (We have already verified it equals 1-6w+9w^2-w^3-w^4.)
    fhat_tex = "1-6w+9w^2-w^3-w^4"

    pi = res.pi
    P = res.P

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_real_input_40_output_potential_zero_temp_ground_sft.py")
    lines.append("\\paragraph{零温缩放极限的 4 状态地基 SFT（可复现）}")
    lines.append("令 $w:=uz^2$ 且 $z=\\sqrt{w/u}$。则当 $u\\to+\\infty$ 且 $w$ 有界固定时，")
    lines.append("由奇次幂项的 $u^{-1/2}$ 衰减得到缩放极限")
    lines.append("$$")
    lines.append(
        "\\widehat F(w):=\\lim_{u\\to+\\infty}F\\!\\left(\\sqrt{w/u},u\\right)"
        f"={fhat_tex}."
    )
    lines.append("$$")
    lines.append("并且该四次多项式可由一个显式 $4\\times4$ 非负整数矩阵表示为一个低阶动力学行列式：")
    lines.append("$$")
    lines.append("\\widehat F(w)=\\det(I-wB_\\infty),\\qquad")
    lines.append("B_\\infty=")
    lines.append("\\begin{pmatrix}")
    for r in range(4):
        lines.append("  " + " & ".join(str(int(x)) for x in B[r]) + ("\\\\" if r != 3 else ""))
    lines.append("\\end{pmatrix}.")
    lines.append("$$")
    lines.append("因此饱和端点的两步 Perron 值满足")
    lines.append("$$")
    lines.append(
        f"\\rho(B_\\infty)\\approx {_fmt_float(res.rho, 12)},\\qquad "
        f"b=\\rho(B_\\infty)^{{-1}}\\approx {_fmt_float(res.b, 12)},\\qquad "
        f"c=\\sqrt{{\\rho(B_\\infty)}}\\approx {_fmt_float(res.c, 12)}."
    )
    lines.append("$$")
    lines.append("并与正文中 $y=c^2$ 的四次方程 $y^4-6y^3+9y^2-y-1=0$ 一致（此处 $y=\\rho(B_\\infty)$）。")
    lines.append("")
    lines.append("进一步，由 $B_\\infty$ 的 Parry 极大熵测度给出零温极限的地基平衡态：")
    lines.append("设 $B_\\infty v=\\rho v$ 且 $v>0$，则转移概率为")
    lines.append("$$")
    lines.append("P_{ij}=\\frac{(B_\\infty)_{ij}v_j}{\\rho v_i},\\qquad \\pi_i\\propto \\ell_i v_i.")
    lines.append("$$")
    lines.append("数值上（按 $12$ 位小数）：")
    lines.append("$$")
    lines.append(
        "\\pi\\approx("
        + ",".join(_fmt_float(float(x), 12) for x in pi)
        + ")."
    )
    lines.append("$$")
    lines.append("$$")
    lines.append("P\\approx\\begin{pmatrix}")
    for r in range(4):
        lines.append(
            "  "
            + " & ".join(_fmt_float(float(P[r][c]), 12) for c in range(4))
            + ("\\\\" if r != 3 else "")
        )
    lines.append("\\end{pmatrix}.")
    lines.append("$$")
    lines.append("在原始一步系统上对应的地基每步熵密度为 $h_{\\mathrm{ground}}=\\tfrac12\\log\\rho(B_\\infty)=\\log c$（参见推论 \\ref{cor:real-input-40-ground-entropy}）。")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Zero-temperature ground SFT reduction for real input 40-state (output potential)."
    )
    parser.add_argument(
        "--progress-seconds",
        type=float,
        default=20.0,
        help="Print a heartbeat progress line every N seconds (0 disables).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(
            export_dir() / "real_input_40_output_potential_zero_temp_ground_sft.json"
        ),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(
            generated_dir()
            / "eq_real_input_40_output_potential_zero_temp_ground_sft.tex"
        ),
    )
    args = parser.parse_args()

    prog = _Progress(enabled=(args.progress_seconds > 0), every_seconds=args.progress_seconds)
    prog.start("computing scaled limit and Parry measure")
    try:
        fhat, coeffs = _leading_scaled_polynomial()
        w = sp.Symbol("w")
        target = sp.expand(1 - 6 * w + 9 * w**2 - w**3 - w**4)
        if sp.expand(fhat - target) != 0:
            raise RuntimeError(f"Unexpected Fhat(w): got {sp.expand(fhat)}, expected {target}")

        B_inf = np.array(
            [
                [0, 1, 1, 0],
                [0, 0, 1, 0],
                [0, 0, 3, 1],
                [1, 0, 0, 3],
            ],
            dtype=int,
        )
        # Verify det(I - w B_inf) equals target.
        det_poly = sp.expand((sp.eye(4) - w * sp.Matrix(B_inf.tolist())).det())
        if sp.expand(det_poly - target) != 0:
            raise RuntimeError("B_inf determinant mismatch.")

        rho, pi, P = _parry_chain_from_adjacency(B_inf)
        b = 1.0 / rho
        c = float(np.sqrt(rho))

        res = ZeroTempGroundSFT(
            fhat_coeffs=coeffs,
            B_inf=B_inf.tolist(),
            rho=float(rho),
            b=float(b),
            c=float(c),
            pi=[float(x) for x in list(pi)],
            P=[[float(x) for x in row] for row in P.tolist()],
        )
        Path(args.json_out).parent.mkdir(parents=True, exist_ok=True)
        Path(args.json_out).write_text(
            json.dumps(asdict(res), indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        _write_tex(Path(args.tex_out), res)
    finally:
        prog.stop("done")


if __name__ == "__main__":
    main()

