#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RH-sharp threshold and error-exponent beta(u) for the pure-collision cubic (4x4 input skeleton).

We work with the 4x4 input-skeleton matrix:

  A_xi(u) = D(u) (F ⊗ F),   D(u)=diag(1,1,1,u),

whose characteristic polynomial factors as:

  det(λI - A_xi(u)) = (λ+1)(λ^3 - 2λ^2 - (u+1)λ + u).

Hence for u>0 the nontrivial spectrum is the three real roots of

  f(λ;u) = λ^3 - 2λ^2 - (u+1)λ + u = 0,

which we order as:
  λ_-(u) < 0 < λ_0(u) < 1 < λ_+(u),
with Perron root λ_+(u).

Define the "worst nontrivial radius" (toy-RH/Ramanujan diagnostic):

  Λ(u) = max{1, |λ_0(u)|, |λ_-(u)|},

and the corresponding error exponent:

  β(u) = log Λ(u) / log λ_+(u)   (with β(u)=0 when Λ(u)=1).

The kernel-RH (Ramanujan) condition Λ(u) <= sqrt(λ_+(u)) holds iff 0<u<=u_R,
where u_R>1 is the unique positive real root of:

  u^5 + 4u^4 + 3u^3 - 96u^2 - 42u - 14 = 0.

This script numerically:
  - computes u_R,
  - reports (λ_+(u_R), λ_0(u_R), λ_-(u_R)) and the RH-sharp equality check
      λ_+(u_R) = (-λ_-(u_R))^2,
  - tabulates β(u) on a small set of sample u-values (including u_R).

Outputs:
  - artifacts/export/arity_pure_collision_cubic_rh_threshold_beta.json
  - sections/generated/eq_arity_pure_collision_cubic_rh_threshold_uR.tex
  - sections/generated/tab_arity_pure_collision_cubic_rh_threshold_beta.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List, Tuple

import mpmath as mp
import sympy as sp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class SampleRow:
    u: str
    lambda_plus: str
    lambda_0: str
    lambda_minus: str
    Lambda: str
    beta: str


@dataclass(frozen=True)
class Payload:
    dps: int
    quintic_uR: str
    u_R: str
    theta_R: str
    # Roots at u_R
    lambda_plus_uR: str
    lambda_0_uR: str
    lambda_minus_uR: str
    check_lambda_plus_minus_sq: str
    beta_uR: str
    beta_uR_minus_half: str
    samples: List[SampleRow]


def _fmt(x: mp.mpf | mp.mpc, nd: int = 16) -> str:
    if isinstance(x, mp.mpc):
        raise TypeError("Use _fmt_re_im for complex numbers.")
    return mp.nstr(x, nd)


def _cubic_roots_ordered(u: mp.mpf) -> Tuple[mp.mpf, mp.mpf, mp.mpf]:
    """
    Return (lambda_plus, lambda_0, lambda_minus) for the cubic f(λ;u)=0.

    For u>0, all three roots are real and distinct (discriminant > 0).
    """
    coeffs = [mp.mpf(1), mp.mpf(-2), -(u + 1), u]
    roots = mp.polyroots(coeffs, maxsteps=200)
    rs: List[mp.mpf] = []
    for r in roots:
        # polyroots returns mpc; imaginary parts should be numerical noise.
        if abs(mp.im(r)) > mp.mpf("1e-30"):
            # Still accept by projecting to real (the cubic is known to have three real roots).
            rs.append(mp.re(r))
        else:
            rs.append(mp.re(r))
    rs = sorted(rs)
    lam_minus, lam_0, lam_plus = rs[0], rs[1], rs[2]
    return lam_plus, lam_0, lam_minus


def _Lambda_and_beta(u: mp.mpf) -> Tuple[mp.mpf, mp.mpf]:
    lam_plus, lam_0, lam_minus = _cubic_roots_ordered(u)
    Lam = max(mp.mpf(1), abs(lam_0), abs(lam_minus))
    if Lam <= 1:
        return Lam, mp.mpf(0)
    return Lam, mp.log(Lam) / mp.log(lam_plus)


def _compute_u_R(*, dps: int) -> mp.mpf:
    u = sp.Symbol("u")
    quintic = u**5 + 4 * u**4 + 3 * u**3 - 96 * u**2 - 42 * u - 14
    P = sp.Poly(quintic, u)
    roots = P.nroots(n=dps, maxsteps=200)
    # Unique positive real root.
    cand: List[sp.Expr] = []
    for r in roots:
        rr = sp.re(r).evalf(dps)
        ii = sp.im(r).evalf(dps)
        if abs(float(ii)) < 1e-30 and float(rr) > 0:
            cand.append(rr)
    if len(cand) != 1:
        raise RuntimeError(f"Expected a unique positive real root, got {len(cand)}: {cand}")
    return mp.mpf(str(cand[0]))


def _write_eq_uR(
    path: Path,
    *,
    u_R: mp.mpf,
    lam_plus: mp.mpf,
    lam_0: mp.mpf,
    lam_minus: mp.mpf,
    beta_uR: mp.mpf,
    check: mp.mpf,
) -> None:
    nd_u = 14
    nd_lam = 16
    lines: List[str] = []
    lines.append("% Auto-generated; do not edit by hand.")
    lines.append(r"\begin{equation}\label{eq:arity_pure_collision_cubic_rh_threshold_uR}")
    lines.append(r"\begin{aligned}")
    lines.append(rf"u_R &\approx {_fmt(u_R, nd_u)},\\")
    lines.append(rf"\lambda_+(u_R) &\approx {_fmt(lam_plus, nd_lam)},\\")
    lines.append(rf"\lambda_0(u_R) &\approx {_fmt(lam_0, nd_lam)},\\")
    lines.append(rf"\lambda_-(u_R) &\approx {_fmt(lam_minus, nd_lam)},\\")
    lines.append(rf"\lambda_+(u_R)-(-\lambda_-(u_R))^2 &\approx {_fmt(check, 18)},\\")
    lines.append(rf"\beta(u_R) &\approx {_fmt(beta_uR, 18)}.")
    lines.append(r"\end{aligned}")
    lines.append(r"\end{equation}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_table(path: Path, rows: List[SampleRow]) -> None:
    lines: List[str] = []
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\scriptsize")
    lines.append(r"\setlength{\tabcolsep}{6pt}")
    lines.append(
        r"\caption{Error-exponent diagnostic for the pure-collision cubic. "
        r"We list the ordered real roots $(\lambda_+,\lambda_0,\lambda_-)$ of "
        r"$\lambda^3-2\lambda^2-(u+1)\lambda+u=0$ for selected $u>0$, "
        r"together with $\Lambda(u)=\max\{1,|\lambda_0|,|\lambda_-|\}$ and "
        r"$\beta(u)=\log\Lambda(u)/\log\lambda_+(u)$.}"
    )
    lines.append(r"\label{tab:arity_pure_collision_cubic_rh_threshold_beta}")
    lines.append(r"\begin{tabular}{r r r r r r}")
    lines.append(r"\toprule")
    lines.append(r"$u$ & $\lambda_+(u)$ & $\lambda_0(u)$ & $\lambda_-(u)$ & $\Lambda(u)$ & $\beta(u)$\\")
    lines.append(r"\midrule")
    for r in rows:
        lines.append(
            f"{r.u} & {r.lambda_plus} & {r.lambda_0} & {r.lambda_minus} & {r.Lambda} & {r.beta}\\\\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute u_R and beta(u) for pure-collision cubic toy-RH.")
    parser.add_argument("--dps", type=int, default=80, help="Working decimal precision (mpmath + sympy nroots).")
    parser.add_argument(
        "--u-samples",
        type=str,
        default="0.5,1,2,3,uR,4,10,100",
        help="Comma-separated u sample values; use literal 'uR' to include the computed u_R.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "arity_pure_collision_cubic_rh_threshold_beta.json"),
    )
    parser.add_argument(
        "--tex-eq-out",
        type=str,
        default=str(generated_dir() / "eq_arity_pure_collision_cubic_rh_threshold_uR.tex"),
    )
    parser.add_argument(
        "--tex-tab-out",
        type=str,
        default=str(generated_dir() / "tab_arity_pure_collision_cubic_rh_threshold_beta.tex"),
    )
    args = parser.parse_args()

    dps = int(args.dps)
    if dps < 50:
        raise SystemExit("Require --dps >= 50 for stable u_R and beta(u) output.")
    mp.mp.dps = dps

    u_R = _compute_u_R(dps=dps)
    theta_R = mp.log(u_R)

    lam_plus_uR, lam_0_uR, lam_minus_uR = _cubic_roots_ordered(u_R)
    Lam_uR = max(mp.mpf(1), abs(lam_0_uR), abs(lam_minus_uR))
    beta_uR = mp.log(Lam_uR) / mp.log(lam_plus_uR)
    check = lam_plus_uR - (abs(lam_minus_uR) ** 2)

    # Build samples.
    toks = [t.strip() for t in str(args.u_samples).split(",") if t.strip()]
    u_vals: List[mp.mpf] = []
    for t in toks:
        if t == "uR":
            u_vals.append(u_R)
        else:
            u_vals.append(mp.mpf(t))

    rows: List[SampleRow] = []
    for uv in u_vals:
        lam_plus, lam_0, lam_minus = _cubic_roots_ordered(uv)
        Lam, beta = _Lambda_and_beta(uv)
        rows.append(
            SampleRow(
                u=_fmt(uv, 12),
                lambda_plus=_fmt(lam_plus, 16),
                lambda_0=_fmt(lam_0, 16),
                lambda_minus=_fmt(lam_minus, 16),
                Lambda=_fmt(Lam, 16),
                beta=_fmt(beta, 12),
            )
        )

    payload = Payload(
        dps=dps,
        quintic_uR="u^5 + 4u^4 + 3u^3 - 96u^2 - 42u - 14",
        u_R=_fmt(u_R, 16),
        theta_R=_fmt(theta_R, 16),
        lambda_plus_uR=_fmt(lam_plus_uR, 24),
        lambda_0_uR=_fmt(lam_0_uR, 24),
        lambda_minus_uR=_fmt(lam_minus_uR, 24),
        check_lambda_plus_minus_sq=_fmt(check, 30),
        beta_uR=_fmt(beta_uR, 24),
        beta_uR_minus_half=_fmt(beta_uR - mp.mpf("0.5"), 30),
        samples=rows,
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[pure-collision-beta] wrote {jout}", flush=True)

    _write_eq_uR(
        Path(args.tex_eq_out),
        u_R=u_R,
        lam_plus=lam_plus_uR,
        lam_0=lam_0_uR,
        lam_minus=lam_minus_uR,
        beta_uR=beta_uR,
        check=check,
    )
    print(f"[pure-collision-beta] wrote {args.tex_eq_out}", flush=True)

    _write_table(Path(args.tex_tab_out), rows)
    print(f"[pure-collision-beta] wrote {args.tex_tab_out}", flush=True)


if __name__ == "__main__":
    main()

