#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Second-order jet of log(Mfrak(theta)) at theta=0 (real-input-40 kernel).

We compute:
- f(0) = log Mfrak(0)
- grad f(0) and Hessian f(0) for theta=(theta_e, theta_neg, theta_2)

using symmetric finite differences and the same Möbius–zeta closed interface
as exp_sync_kernel_real_input_40_logM_theta.py.

Outputs (default):
- artifacts/export/sync_kernel_real_input_40_logM_theta_taylor.json
- sections/generated/tab_real_input_40_logM_theta_taylor.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from exp_sync_kernel_real_input_40 import build_kernel_edges, build_kernel_map, build_real_input_states
from exp_sync_kernel_real_input_40_logM_theta import logM_theta


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _fmt(x: float) -> str:
    # stable latex-friendly formatting
    return f"{x:.12g}"


def _latex_table(grad: np.ndarray, hess: np.ndarray, f0: float, *, h: float, k_max: int) -> str:
    # Row labels must be in math mode inside tabular.
    names = [r"$\theta_e$", r"$\theta_-$", r"$\theta_2$"]
    lines: List[str] = []
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\scriptsize")
    lines.append(r"\setlength{\tabcolsep}{8pt}")
    lines.append(r"\renewcommand{\arraystretch}{1.2}")
    lines.append(
        rf"\caption{{$\log\mathfrak{{M}}(\theta)$ 在 $\theta=0$ 的二阶展开系数（真实输入 40 状态核；对称差分步长 $h={_fmt(h)}$；Möbius 尾截断 $k_{{\max}}={k_max}$；脚本生成）。}}"
    )
    lines.append(r"\label{tab:real-input-40-logM-theta-taylor}")
    lines.append(r"\begin{tabular}{@{}lccc@{}}")
    lines.append(r"\toprule")
    lines.append(r" & \multicolumn{3}{c}{方向} \\")
    lines.append(r"\cmidrule(lr){2-4}")
    lines.append(r" & $\theta_e$ & $\theta_-$ & $\theta_2$ \\")
    lines.append(r"\midrule")
    lines.append(rf"$\log\mathfrak{{M}}(0)$ & \multicolumn{{3}}{{c}}{{{_fmt(f0)}}} \\")
    lines.append(r"\midrule")
    lines.append(r"$\nabla\log\mathfrak{M}(0)$ & " + " & ".join(_fmt(float(grad[i])) for i in range(3)) + r" \\")
    lines.append(r"\midrule")
    lines.append(r"$\nabla^2\log\mathfrak{M}(0)$ &  &  &  \\")
    for i in range(3):
        lines.append(
            rf"{names[i]} & "
            + " & ".join(_fmt(float(hess[i, j])) for j in range(3))
            + r" \\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    return "\n".join(lines) + "\n"


@dataclass(frozen=True)
class Theta:
    e: float
    neg: float
    two: float


def _eval_logm(
    theta: Theta,
    *,
    k_max: int,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
    prog: Progress,
    tag: str,
) -> float:
    _, logm = logM_theta(
        theta_e=theta.e,
        theta_neg=theta.neg,
        theta_2=theta.two,
        k_max=k_max,
        states=states,
        kernel_map=kernel_map,
        prog=prog,
        tag=tag,
    )
    return float(logm)


def main() -> None:
    parser = argparse.ArgumentParser(description="Second-order jet of log Mfrak(theta) at theta=0 (real-input-40)")
    parser.add_argument("--h", type=float, default=2e-4, help="Finite-difference step")
    parser.add_argument("--k-max", type=int, default=200, help="Max k for Möbius tail series")
    parser.add_argument("--no-output", action="store_true")
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/sync_kernel_real_input_40_logM_theta_taylor.json)",
    )
    args = parser.parse_args()

    h = float(args.h)
    if not (h > 0.0 and math.isfinite(h)):
        raise SystemExit("--h must be positive and finite")

    k_max = int(args.k_max)
    if k_max < 10:
        raise SystemExit("--k-max too small (>=10 recommended)")

    prog = Progress(label="real-input-40-logM-theta-taylor", every_seconds=20.0)
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()

    # Base point
    f0 = _eval_logm(Theta(0.0, 0.0, 0.0), k_max=k_max, states=states, kernel_map=kernel_map, prog=prog, tag="0")

    # Univariate points for gradient/diagonal Hessian
    basis = [
        Theta(+h, 0.0, 0.0),
        Theta(-h, 0.0, 0.0),
        Theta(0.0, +h, 0.0),
        Theta(0.0, -h, 0.0),
        Theta(0.0, 0.0, +h),
        Theta(0.0, 0.0, -h),
    ]
    vals = [
        _eval_logm(th, k_max=k_max, states=states, kernel_map=kernel_map, prog=prog, tag=f"axis-{i}")
        for i, th in enumerate(basis)
    ]

    f_ep, f_em, f_np, f_nm, f_tp, f_tm = vals

    grad = np.zeros(3, dtype=float)
    grad[0] = (f_ep - f_em) / (2.0 * h)
    grad[1] = (f_np - f_nm) / (2.0 * h)
    grad[2] = (f_tp - f_tm) / (2.0 * h)

    hess = np.zeros((3, 3), dtype=float)
    hess[0, 0] = (f_ep - 2.0 * f0 + f_em) / (h * h)
    hess[1, 1] = (f_np - 2.0 * f0 + f_nm) / (h * h)
    hess[2, 2] = (f_tp - 2.0 * f0 + f_tm) / (h * h)

    # Mixed partials
    def mix(i: int, j: int) -> float:
        # central mixed second derivative using 4 corners
        # ( +,+ ) - ( +,- ) - ( -,+ ) + ( -,- ) / (4 h^2)
        def th(s1: float, s2: float) -> Theta:
            e = 0.0
            neg = 0.0
            two = 0.0
            if i == 0:
                e += s1
            elif i == 1:
                neg += s1
            else:
                two += s1
            if j == 0:
                e += s2
            elif j == 1:
                neg += s2
            else:
                two += s2
            return Theta(e, neg, two)

        f_pp = _eval_logm(th(+h, +h), k_max=k_max, states=states, kernel_map=kernel_map, prog=prog, tag=f"mix-{i}{j}-pp")
        f_pm = _eval_logm(th(+h, -h), k_max=k_max, states=states, kernel_map=kernel_map, prog=prog, tag=f"mix-{i}{j}-pm")
        f_mp = _eval_logm(th(-h, +h), k_max=k_max, states=states, kernel_map=kernel_map, prog=prog, tag=f"mix-{i}{j}-mp")
        f_mm = _eval_logm(th(-h, -h), k_max=k_max, states=states, kernel_map=kernel_map, prog=prog, tag=f"mix-{i}{j}-mm")
        return (f_pp - f_pm - f_mp + f_mm) / (4.0 * h * h)

    for (i, j) in [(0, 1), (0, 2), (1, 2)]:
        v = mix(i, j)
        hess[i, j] = v
        hess[j, i] = v

    # Report a compact sample to stdout.
    print(
        f"[real-input-40-logM-theta-taylor] f0={f0:.12g} "
        f"grad=({_fmt(grad[0])},{_fmt(grad[1])},{_fmt(grad[2])})",
        flush=True,
    )

    payload: Dict[str, object] = {
        "h": h,
        "k_max": k_max,
        "logM_0": f0,
        "grad_logM_0": grad.tolist(),
        "hess_logM_0": hess.tolist(),
        "gamma": 0.5772156649015329,
    }

    if args.no_output:
        return

    out_json = Path(args.output) if args.output else export_dir() / "sync_kernel_real_input_40_logM_theta_taylor.json"
    out_tex = generated_dir() / "tab_real_input_40_logM_theta_taylor.tex"
    _write_json(out_json, payload)
    _write_text(out_tex, _latex_table(grad, hess, f0, h=h, k_max=k_max))
    print(f"[real-input-40-logM-theta-taylor] wrote {out_json}", flush=True)
    print(f"[real-input-40-logM-theta-taylor] wrote {out_tex}", flush=True)
    print("[real-input-40-logM-theta-taylor] done", flush=True)


if __name__ == "__main__":
    main()

