#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Closed-form cumulants for the real-input 40-state kernel, output potential only.

We weight only the output-bit observable e in {0,1} by u^e, with u = exp(theta),
and use the explicit degree-8 algebraic curve G(lambda,u)=0 for the Perron root
lambda(u)=rho(M(u)).

We compute the Taylor expansion of:
  P(theta) := log lambda(exp(theta))
around theta=0 (u=1) up to order 4, and output closed forms in Q(sqrt(5)).

Outputs:
  - artifacts/export/real_input_40_output_potential_cumulants_closed.json
  - sections/generated/tab_real_input_40_output_potential_cumulants_closed.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import threading
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Dict, Optional

import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class CumulantsClosed:
    # P^(k)(0) for k=1..4
    P1: str
    P2: str
    P3: str
    P4: str
    # decimals
    P1_float: str
    P2_float: str
    P3_float: str
    P4_float: str
    # lambda(1)
    lambda0: str


class _Progress:
    def __init__(
        self, *, enabled: bool, every_seconds: float, prefix: str = "[output-cumulants]"
    ) -> None:
        self._enabled = enabled and every_seconds > 0
        self._every_seconds = float(every_seconds)
        self._prefix = prefix
        self._stop = threading.Event()
        self._thread: Optional[threading.Thread] = None
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


def _series_P_derivatives(log: Optional[Callable[[str], None]] = None) -> Dict[str, sp.Expr]:
    theta = sp.Symbol("theta")
    u = sp.exp(theta)
    lam0 = (sp.Integer(3) + sp.sqrt(5)) / 2  # phi^2

    c1, c2, c3, c4 = sp.symbols("c1 c2 c3 c4")
    lam_series = lam0 + c1 * theta + c2 * theta**2 + c3 * theta**3 + c4 * theta**4

    lam = sp.Symbol("lam")
    uu = sp.Symbol("u")
    G = _build_G(lam, uu)

    # Expand G(lam(theta), exp(theta)) and solve coefficients.
    if log is not None:
        log("building series constraints up to order 4")
    expr = sp.expand(G.subs({lam: lam_series, uu: u}))
    ser = sp.series(expr, theta, 0, 5).removeO()
    ser_exp = sp.expand(ser)
    e0 = sp.simplify(ser_exp.coeff(theta, 0))
    e1 = sp.simplify(ser_exp.coeff(theta, 1))
    e2 = sp.simplify(ser_exp.coeff(theta, 2))
    e3 = sp.simplify(ser_exp.coeff(theta, 3))
    e4 = sp.simplify(ser_exp.coeff(theta, 4))

    if log is not None:
        log("solving lambda-series coefficients (c1..c4)")
    # Coefficient at theta^0 should be 0 automatically if lam0 is correct; keep for safety.
    if e0 != 0:
        raise RuntimeError("Series constant term is nonzero; lambda0 may be incorrect.")

    # Solve sequentially; each equation is linear in the next coefficient.
    s1 = sp.solve(e1, c1, dict=True)
    if not s1:
        raise RuntimeError("No solution for c1.")
    sol1 = s1[0]
    if log is not None:
        log("solved c1")

    e2s = sp.simplify(e2.subs(sol1))
    s2 = sp.solve(e2s, c2, dict=True)
    if not s2:
        raise RuntimeError("No solution for c2.")
    sol2 = {**sol1, **s2[0]}
    if log is not None:
        log("solved c2")

    e3s = sp.simplify(e3.subs(sol2))
    s3 = sp.solve(e3s, c3, dict=True)
    if not s3:
        raise RuntimeError("No solution for c3.")
    sol3 = {**sol2, **s3[0]}
    if log is not None:
        log("solved c3")

    e4s = sp.simplify(e4.subs(sol3))
    s4 = sp.solve(e4s, c4, dict=True)
    if not s4:
        raise RuntimeError("No solution for c4.")
    sol4 = {**sol3, **s4[0]}
    if log is not None:
        log("solved c4")

    lam_series = sp.expand(lam_series.subs(sol4))
    if log is not None:
        log("deriving P(theta)=log lambda(exp(theta))")
    P_series = sp.series(sp.log(lam_series), theta, 0, 5).removeO()

    # Extract derivatives: P(theta)=P0 + P1 theta + P2/2 theta^2 + ...
    if log is not None:
        log("extracting derivatives at theta=0")
    P1 = sp.simplify(sp.diff(P_series, theta, 1).subs(theta, 0))
    P2 = sp.simplify(sp.diff(P_series, theta, 2).subs(theta, 0))
    P3 = sp.simplify(sp.diff(P_series, theta, 3).subs(theta, 0))
    P4 = sp.simplify(sp.diff(P_series, theta, 4).subs(theta, 0))

    return {"lambda0": lam0, "P1": P1, "P2": P2, "P3": P3, "P4": P4}


def _as_float_str(x: sp.Expr, n: int = 16) -> str:
    return sp.N(x, n).__str__()


def _tex_table(path: Path, res: CumulantsClosed) -> None:
    lines: list[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Closed-form cumulants for the output potential of the real-input 40-state kernel. "
        "We weight only $e\\in\\{0,1\\}$ by $u^e$ with $u=e^{\\theta}$ and define $P(\\theta)=\\log\\lambda(e^{\\theta})$. "
        "Derivatives at $\\theta=0$ lie in $\\mathbb{Q}(\\sqrt5)$ and are derived from the degree-8 curve $G(\\lambda,u)=0$.}"
    )
    lines.append("\\label{tab:real_input_40_output_potential_cumulants_closed}")
    lines.append("\\begin{tabular}{l l l}")
    lines.append("\\toprule")
    lines.append("quantity & closed form & decimal \\\\")
    lines.append("\\midrule")
    lam0 = sp.sympify(res.lambda0)
    P1 = sp.sympify(res.P1)
    P2 = sp.sympify(res.P2)
    P3 = sp.sympify(res.P3)
    P4 = sp.sympify(res.P4)
    lines.append(
        f"$\\lambda(1)$ & ${sp.latex(lam0)}$ & ${_as_float_str(lam0, 18)}$\\\\"
    )
    lines.append(f"$P'(0)$ & ${sp.latex(P1)}$ & ${res.P1_float}$\\\\")
    lines.append(f"$P''(0)$ & ${sp.latex(P2)}$ & ${res.P2_float}$\\\\")
    lines.append(f"$P^{{(3)}}(0)$ & ${sp.latex(P3)}$ & ${res.P3_float}$\\\\")
    lines.append(f"$P^{{(4)}}(0)$ & ${sp.latex(P4)}$ & ${res.P4_float}$\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Closed-form cumulants for output potential (real input 40-state)."
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
            export_dir() / "real_input_40_output_potential_cumulants_closed.json"
        ),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(
            generated_dir() / "tab_real_input_40_output_potential_cumulants_closed.tex"
        ),
    )
    args = parser.parse_args()

    prog = _Progress(
        enabled=(args.progress_seconds > 0),
        every_seconds=float(args.progress_seconds),
    )
    prog.start("starting symbolic derivation")
    try:
        d = _series_P_derivatives(log=lambda s: print(f"[output-cumulants] {s}", flush=True))
    finally:
        prog.stop("symbolic derivation finished")
    lam0 = sp.simplify(d["lambda0"])
    P1 = sp.simplify(d["P1"])
    P2 = sp.simplify(d["P2"])
    P3 = sp.simplify(d["P3"])
    P4 = sp.simplify(d["P4"])

    res = CumulantsClosed(
        lambda0=str(lam0),
        P1=str(P1),
        P2=str(P2),
        P3=str(P3),
        P4=str(P4),
        P1_float=_as_float_str(P1, 18),
        P2_float=_as_float_str(P2, 18),
        P3_float=_as_float_str(P3, 18),
        P4_float=_as_float_str(P4, 18),
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(
        json.dumps(asdict(res), indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(f"[output-cumulants] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    _tex_table(tout, res)
    print(f"[output-cumulants] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()
