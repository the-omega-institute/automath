#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Asymptotic-rate audit for beta(u) in the pure-collision cubic (4x4 input skeleton).

We study the cubic eigenproblem

  f(λ;u) = λ^3 - 2λ^2 - (u+1)λ + u = 0,   u>0,

with ordered real roots

  λ_-(u) < 0 < λ_0(u) < 1 < λ_+(u).

Define

  Λ(u) = max{1, |λ_0(u)|, |λ_-(u)|},   β(u) = log Λ(u) / log λ_+(u),

where β(u)=0 when Λ(u)=1.

For large u, the extreme roots admit Puiseux expansions

  λ_+(u) = sqrt(u) + 1/2 + 9/(8 sqrt(u)) + O(u^{-1}),
  λ_-(u) = -sqrt(u) + 1/2 - 9/(8 sqrt(u)) + O(u^{-1}),

hence β(u) = 1 - 2/(sqrt(u) log u) + O(1/(u log u)).

This script tabulates the scaled residuals to audit the asymptotic rate.

Outputs:
  - artifacts/export/arity_pure_collision_cubic_beta_asymptotic_rate.json
  - sections/generated/tab_arity_pure_collision_cubic_beta_asymptotic_rate.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List, Tuple

import mpmath as mp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class Row:
    u: str
    beta: str
    beta_asymp: str
    diff: str
    scaled_sqrtu_logu_1_minus_beta: str
    scaled_ulogudiff: str


@dataclass(frozen=True)
class Payload:
    dps: int
    beta_asymp_formula: str
    rows: List[Row]


def _fmt(x: mp.mpf, nd: int = 18) -> str:
    return mp.nstr(x, nd)


def _cubic_roots_ordered(u: mp.mpf) -> Tuple[mp.mpf, mp.mpf, mp.mpf]:
    """
    Return (lambda_plus, lambda_0, lambda_minus) for the cubic f(λ;u)=0.

    For u>0, all three roots are real and distinct (discriminant > 0).
    """
    coeffs = [mp.mpf(1), mp.mpf(-2), -(u + 1), u]
    roots = mp.polyroots(coeffs, maxsteps=400)
    rs: List[mp.mpf] = [mp.re(r) for r in roots]
    rs = sorted(rs)
    lam_minus, lam_0, lam_plus = rs[0], rs[1], rs[2]
    return lam_plus, lam_0, lam_minus


def _Lambda_and_beta(u: mp.mpf) -> Tuple[mp.mpf, mp.mpf]:
    lam_plus, lam_0, lam_minus = _cubic_roots_ordered(u)
    Lam = max(mp.mpf(1), abs(lam_0), abs(lam_minus))
    if Lam <= 1:
        return Lam, mp.mpf(0)
    return Lam, mp.log(Lam) / mp.log(lam_plus)


def _write_table(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\scriptsize")
    lines.append(r"\setlength{\tabcolsep}{5pt}")
    lines.append(
        r"\caption{Asymptotic-rate audit for the pure-collision cubic exponent $\beta(u)$. "
        r"We compare $\beta(u)$ to $\beta_{\mathrm{asymp}}(u):=1-\frac{2}{\sqrt u\,\log u}$ "
        r"and report the scaled residuals.}"
    )
    lines.append(r"\label{tab:arity_pure_collision_cubic_beta_asymptotic_rate}")
    lines.append(r"\begin{tabular}{r r r r r r}")
    lines.append(r"\toprule")
    lines.append(
        r"$u$ & $\beta(u)$ & $\beta_{\mathrm{asymp}}(u)$ & $\beta-\beta_{\mathrm{asymp}}$ "
        r"& $\sqrt u\,\log u\,(1-\beta)$ & $u\,\log u\,(\beta-\beta_{\mathrm{asymp}})$\\"
    )
    lines.append(r"\midrule")
    for r in rows:
        lines.append(
            f"{r.u} & {r.beta} & {r.beta_asymp} & {r.diff} & "
            f"{r.scaled_sqrtu_logu_1_minus_beta} & {r.scaled_ulogudiff}\\\\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit beta(u) asymptotic rate for pure-collision cubic.")
    parser.add_argument("--dps", type=int, default=80, help="Working decimal precision (mpmath).")
    parser.add_argument(
        "--u-samples",
        type=str,
        default="100,10000,1000000",
        help="Comma-separated u sample values (suggest: large u>1).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "arity_pure_collision_cubic_beta_asymptotic_rate.json"),
    )
    parser.add_argument(
        "--tex-tab-out",
        type=str,
        default=str(generated_dir() / "tab_arity_pure_collision_cubic_beta_asymptotic_rate.tex"),
    )
    args = parser.parse_args()

    dps = int(args.dps)
    if dps < 50:
        raise SystemExit("Require --dps >= 50 for stable beta(u) output.")
    mp.mp.dps = dps

    toks = [t.strip() for t in str(args.u_samples).split(",") if t.strip()]
    u_vals: List[mp.mpf] = [mp.mpf(t) for t in toks]

    rows: List[Row] = []
    for uv in u_vals:
        Lam, beta = _Lambda_and_beta(uv)
        if uv <= 1:
            beta_asymp = mp.mpf("nan")
            diff = mp.mpf("nan")
            scaled1 = mp.mpf("nan")
            scaled2 = mp.mpf("nan")
        else:
            beta_asymp = mp.mpf(1) - mp.mpf(2) / (mp.sqrt(uv) * mp.log(uv))
            diff = beta - beta_asymp
            scaled1 = mp.sqrt(uv) * mp.log(uv) * (mp.mpf(1) - beta)
            scaled2 = uv * mp.log(uv) * diff

        rows.append(
            Row(
                u=_fmt(uv, 12),
                beta=_fmt(beta, 18),
                beta_asymp=_fmt(beta_asymp, 18) if uv > 1 else "nan",
                diff=_fmt(diff, 18) if uv > 1 else "nan",
                scaled_sqrtu_logu_1_minus_beta=_fmt(scaled1, 18) if uv > 1 else "nan",
                scaled_ulogudiff=_fmt(scaled2, 18) if uv > 1 else "nan",
            )
        )

    payload = Payload(
        dps=dps,
        beta_asymp_formula="1 - 2/(sqrt(u) log u)",
        rows=rows,
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[pure-collision-beta-asymptotic] wrote {jout}", flush=True)

    _write_table(Path(args.tex_tab_out), rows)
    print(f"[pure-collision-beta-asymptotic] wrote {args.tex_tab_out}", flush=True)


if __name__ == "__main__":
    main()

