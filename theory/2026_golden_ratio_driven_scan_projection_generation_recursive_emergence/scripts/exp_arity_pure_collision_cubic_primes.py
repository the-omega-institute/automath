#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Pure-collision slow-mode spectrum along ((3,3,p)) via the cubic equation.

For u on the unit circle, the 4x4 input-skeleton twist A_xi(u)=D(u)(F⊗F)
has eigenvalues -1 and the roots of:
  λ^3 - 2λ^2 - (u+1)λ + u = 0.

For each odd prime p we evaluate u=ω_p^j and take:
  rho_p = max_{1<=j<=p-1} ρ(A_xi(ω_p^j)),
then report:
  ratio = rho_p / ρ(A_xi(1)) = rho_p / φ^2,
  tau_mix(p) = 1 / (-log(ratio)).

We also compare with the small-angle asymptotic using closed-form coefficients:
  log ratio = -kappa_inf * α^2 + beta * α^4 + O(α^6),
  α = 2π/p.

Outputs:
  - artifacts/export/arity_pure_collision_cubic_primes.json
  - sections/generated/tab_arity_pure_collision_cubic_primes.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List

import mpmath as mp

from common_paths import export_dir, generated_dir


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def primes_up_to(n: int) -> List[int]:
    return [p for p in range(2, n + 1) if _is_prime(p)]


def rho_from_u(u: mp.mpc) -> mp.mpf:
    # eigenvalues are -1 and roots of cubic
    coeffs = [mp.mpc(1), mp.mpc(-2), -(u + 1), u]
    roots = mp.polyroots(coeffs)
    cand = [mp.mpf(1)]  # |-1|
    for r in roots:
        cand.append(abs(r))
    return max(cand)


@dataclass(frozen=True)
class Row:
    p: int
    j_star: int
    rho: str
    ratio: str
    tau_mix: str
    kappa_p: str
    ratio_asymp2: str
    ratio_asymp4: str


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute pure-collision cubic slow modes for primes p.")
    parser.add_argument("--p-max", type=int, default=101)
    parser.add_argument("--dps", type=int, default=80)
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "arity_pure_collision_cubic_primes.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_arity_pure_collision_cubic_primes.tex"),
    )
    args = parser.parse_args()

    mp.mp.dps = int(args.dps)
    phi = (1 + mp.sqrt(5)) / 2
    lam0 = phi**2  # ρ(A_xi(1))

    # Closed-form coefficients (keep as mp floats; exact forms are in a separate table).
    kappa_inf = (6 * mp.sqrt(5) - 5) / 250  # P''(0)/2
    beta = (7 + 24 * mp.sqrt(5)) / 75000  # P^{(4)}(0)/24

    ps = [p for p in primes_up_to(int(args.p_max)) if p % 2 == 1]

    rows: List[Row] = []
    for p in ps:
        w = mp.e ** (2 * mp.pi * mp.j / p)
        best_rho = mp.mpf("0")
        best_j = 1
        for j in range(1, p):
            u = w**j
            r = rho_from_u(u)
            if r > best_rho:
                best_rho = r
                best_j = j
        ratio = best_rho / lam0
        tau_mix = 1 / (-mp.log(ratio))
        alpha = 2 * mp.pi / p
        ratio_as2 = mp.e ** (-kappa_inf * alpha**2)
        ratio_as4 = mp.e ** (-kappa_inf * alpha**2 + beta * alpha**4)
        kappa_p = (1 - ratio) / (alpha**2)
        rows.append(
            Row(
                p=p,
                j_star=best_j,
                rho=mp.nstr(best_rho, 18),
                ratio=mp.nstr(ratio, 18),
                tau_mix=mp.nstr(tau_mix, 18),
                kappa_p=mp.nstr(kappa_p, 18),
                ratio_asymp2=mp.nstr(ratio_as2, 18),
                ratio_asymp4=mp.nstr(ratio_as4, 18),
            )
        )
        print(f"[pure-collision-cubic] p={p} j*={best_j} ratio={mp.nstr(ratio, 12)}", flush=True)

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps({"p_max": int(args.p_max), "dps": int(args.dps), "rows": [asdict(r) for r in rows]}, indent=2) + "\n", encoding="utf-8")
    print(f"[pure-collision-cubic] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Pure-collision slow-mode spectrum for $((3,3,p))$ along the $N_2\\bmod p$ axis, "
        "computed analytically from the cubic equation on the 4-state input skeleton "
        "$A_\\xi(u)=D(u)(F\\otimes F)$. Here $\\lambda=\\rho(A_\\xi(1))=\\varphi^2$, "
        "$\\rho_{3,3,p}:=\\max_{1\\le j\\le p-1}\\rho(A_\\xi(\\omega_p^j))$, and "
        "$\\tau_{\\mathrm{mix}}(p)=1/(-\\log(\\rho_{3,3,p}/\\lambda))$.}"
    )
    lines.append("\\label{tab:arity_pure_collision_cubic_primes}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append("$p$ & $j_\\star$ & $\\rho_{3,3,p}/\\lambda$ & $\\tau_{\\mathrm{mix}}(p)$ & $\\kappa_p$ & asymp $\\exp(-\\kappa_\\infty\\alpha^2+\\beta\\alpha^4)$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(f"{r.p} & {r.j_star} & {r.ratio} & {r.tau_mix} & {r.kappa_p} & {r.ratio_asymp4}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[pure-collision-cubic] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

