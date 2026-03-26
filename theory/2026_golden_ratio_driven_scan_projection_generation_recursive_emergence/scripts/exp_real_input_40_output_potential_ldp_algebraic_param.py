#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Algebraic parametrization of the output-potential LDP for the real-input 40-state kernel.

We weight only the output bit e in {0,1} by u^e (u = exp(theta)). The pressure is:
  P(theta) = log lambda(u),  u = exp(theta),
where lambda(u) is the Perron root of M(u). From the explicit determinant factorization,
lambda(u) is characterized as the maximal positive real root of the degree-8 curve:
  G(lambda,u) = 0.

The equilibrium output density is:
  alpha(u) = d/dtheta log lambda(exp(theta)) = u * lambda'(u) / lambda(u).

Using implicit differentiation of G(lambda(u),u)=0, one obtains a fully explicit formula:
  alpha(u) = - u * (∂_u G)/(lambda * ∂_lambda G) evaluated at lambda=lambda(u).

The LDP rate function along the same parametrization is:
  I(alpha(u)) = alpha(u) log u - log(lambda(u)/lambda(1)).

This script emits a TeX snippet with both the invariant implicit-derivative form and an
expanded rational expression for alpha(u) in terms of (u,lambda), plus the parametric
formula for I(alpha(u)).

Outputs:
  - artifacts/export/real_input_40_output_potential_ldp_algebraic_param.json
  - sections/generated/eq_real_input_40_output_potential_ldp_algebraic_param.tex
"""

from __future__ import annotations

import argparse
import json
import threading
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class LdpAlgebraicParam:
    # alpha(u,lam) = N / D where N,D are polynomials in (u,lam)
    numerator: str
    denominator: str


class _Progress:
    def __init__(
        self, *, enabled: bool, every_seconds: float, prefix: str = "[ldp-param]"
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


def _build_G(lam: sp.Symbol, u: sp.Symbol) -> sp.Expr:
    # Must match `sections/appendix/sync_kernel/real_input/app__real-input-40-zeta-u.tex`.
    return (
        lam**8
        - lam**7
        - 6 * u * lam**6
        + 2 * u * lam**5
        + (9 * u**2 - u) * lam**4
        + (u - 3 * u**2) * lam**3
        - (u**3 + 2 * u**2) * lam**2
        + (4 * u**3 - 3 * u**2) * lam
        + (u**3 - u**4)
    )


def _alpha_rational() -> Tuple[sp.Expr, sp.Expr]:
    lam, u = sp.Symbol("lam"), sp.Symbol("u")
    G = _build_G(lam, u)
    Gu = sp.diff(G, u)
    Gl = sp.diff(G, lam)
    alpha = sp.simplify(-u * Gu / (lam * Gl))
    # Put into N/D with N,D polynomials.
    frac = sp.together(alpha)
    num, den = sp.fraction(frac)
    num = sp.expand(num)
    den = sp.expand(den)
    return num, den


def _add_expr_multiline_tex(
    expr: sp.Expr, *, symbol_names: Dict[sp.Symbol, str], max_line_len: int
) -> list[str]:
    expr = sp.expand(expr)
    if expr == 0:
        return ["0"]

    if not expr.is_Add:
        return [sp.latex(expr, symbol_names=symbol_names).strip()]

    terms = sp.Add.make_args(expr)
    pieces: list[str] = []
    for i, t in enumerate(terms):
        if i == 0:
            pieces.append(sp.latex(t, symbol_names=symbol_names).strip())
            continue

        if t.could_extract_minus_sign():
            pieces.append("- " + sp.latex(-t, symbol_names=symbol_names).strip())
        else:
            pieces.append("+ " + sp.latex(t, symbol_names=symbol_names).strip())

    lines: list[str] = []
    cur = ""
    for p in pieces:
        if not cur:
            cur = p
            continue
        if len(cur) + 1 + len(p) <= max_line_len:
            cur = cur + " " + p
        else:
            lines.append(cur)
            cur = p
    if cur:
        lines.append(cur)
    return lines


def _write_tex(path: Path, res: LdpAlgebraicParam) -> None:
    lam, u = sp.Symbol("lam"), sp.Symbol("u")
    num = sp.sympify(res.numerator, locals={"lam": lam, "u": u})
    den = sp.sympify(res.denominator, locals={"lam": lam, "u": u})
    sym_names = {lam: r"\lambda"}

    lines: list[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_real_input_40_output_potential_ldp_algebraic_param.py")
    lines.append("\\paragraph{输出位势的大偏差：代数参数化（可复现）}")
    lines.append("令 $u=e^{\\theta}$ 且 $\\lambda(u)=\\rho(M(u))$ 为 $G(\\lambda,u)=0$ 的最大正实根（命题 \\ref{prop:real-input-40-pressure-freezing}）。")
    lines.append("则平衡态下输出 $1$ 的典型密度满足")
    lines.append("$$")
    lines.append(
        "\\alpha(u):=\\frac{d}{d\\theta}\\log\\lambda(e^{\\theta})"
        "=\\frac{u\\,\\lambda'(u)}{\\lambda(u)}"
        "=-\\frac{u\\,\\partial_u G(\\lambda,u)}{\\lambda\\,\\partial_{\\lambda}G(\\lambda,u)}\\Bigg|_{\\lambda=\\lambda(u)}."
    )
    lines.append("$$")
    lines.append("对本核的显式 $G$ 展开偏导后，上式可写为完全有理形式（其中分子分母均为多项式）：")
    lines.append("$$")
    num_lines = _add_expr_multiline_tex(num, symbol_names=sym_names, max_line_len=75)
    den_lines = _add_expr_multiline_tex(den, symbol_names=sym_names, max_line_len=75)
    lines.append("\\begin{aligned}")
    lines.append(
        "\\alpha(u)&=\\left.\\frac{N(\\lambda,u)}{D(\\lambda,u)}\\right|_{\\lambda=\\lambda(u)}."
        "\\\\"
    )
    lines.append(f"N(\\lambda,u)&={num_lines[0]}\\\\")
    for ln in num_lines[1:]:
        lines.append(f"&\\qquad {ln}\\\\")
    lines.append(f"D(\\lambda,u)&={den_lines[0]}\\\\")
    for ln in den_lines[1:-1]:
        lines.append(f"&\\qquad {ln}\\\\")
    if len(den_lines) > 1:
        lines.append(f"&\\qquad {den_lines[-1]}")
    else:
        lines[-1] = lines[-1].rstrip("\\\\")
    lines.append("\\end{aligned}")
    lines.append("$$")
    lines.append("相应的大偏差率函数（Legendre 对偶）沿同一参数 $u$ 具有显式参数表示：")
    lines.append("$$")
    lines.append(
        "I(\\alpha(u))=\\alpha(u)\\log u-\\log\\frac{\\lambda(u)}{\\lambda(1)}."
    )
    lines.append("$$")
    lines.append("由于同时满足 $G(\\lambda,u)=0$ 与上式的有理约束，故 $(\\alpha,u)$ 或 $(\\alpha,\\lambda)$ 之间可通过消元得到一条代数曲线，从而端点展开与代数误差界均可在符号层面审计。")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Algebraic LDP parametrization for output potential (real input 40-state)."
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
            export_dir() / "real_input_40_output_potential_ldp_algebraic_param.json"
        ),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(
            generated_dir()
            / "eq_real_input_40_output_potential_ldp_algebraic_param.tex"
        ),
    )
    args = parser.parse_args()

    prog = _Progress(enabled=(args.progress_seconds > 0), every_seconds=args.progress_seconds)
    prog.start("deriving alpha(u) rational form")
    try:
        num, den = _alpha_rational()
        out = LdpAlgebraicParam(numerator=sp.sstr(num), denominator=sp.sstr(den))
        Path(args.json_out).parent.mkdir(parents=True, exist_ok=True)
        Path(args.json_out).write_text(
            json.dumps(asdict(out), indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        _write_tex(Path(args.tex_out), out)
    finally:
        prog.stop("done")


if __name__ == "__main__":
    main()

