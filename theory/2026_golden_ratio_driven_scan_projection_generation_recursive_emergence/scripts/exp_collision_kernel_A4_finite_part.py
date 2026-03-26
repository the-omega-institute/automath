#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Abel/Mertens finite-part constants for the 4th-collision kernel A4.

We treat A4 as an SFT adjacency matrix and compute the Abel/Hadamard finite-part
constant log 𝔐 and the orbit-Mertens constant 𝕄 = γ + log 𝔐, using:

  log 𝔐 = log C + Σ_{k>=2} μ(k)/k * log ζ(z_*^k),

where:
  - ζ(z) = 1/det(I - z A4) = 1/Δ(z),
  - z_* = 1/ρ(A4) is the main pole,
  - C = lim_{z->z_*} (1 - ρ z) ζ(z) = 1/(-z_* Δ'(z_*)).

Here Δ(z) is explicitly known from the verified order-5 recurrence for S4:
  Δ(z)=det(I-zA4)=1 - 2z - 7z^2 - 2z^4 + 2z^5.

Outputs (default):
  - artifacts/export/collision_kernel_A4_finite_part.json
  - sections/generated/tab_collision_kernel_A4_finite_part.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


def delta(z: float) -> float:
    # Δ(z)=1 - 2z - 7z^2 - 2z^4 + 2z^5
    z2 = z * z
    z4 = z2 * z2
    return 1.0 - 2.0 * z - 7.0 * z2 - 2.0 * z4 + 2.0 * z4 * z


def delta_prime(z: float) -> float:
    # Δ'(z)= -2 -14 z -8 z^3 +10 z^4
    z2 = z * z
    z3 = z2 * z
    z4 = z2 * z2
    return -2.0 - 14.0 * z - 8.0 * z3 + 10.0 * z4


def zeta(z: float) -> float:
    return 1.0 / delta(z)


def mobius_upto(n: int) -> List[int]:
    mu = [0] * (n + 1)
    mu[0] = 0
    mu[1] = 1
    primes: List[int] = []
    is_comp = [False] * (n + 1)
    for i in range(2, n + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n:
                break
            is_comp[i * p] = True
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def perron_root_r4(iters: int = 80) -> float:
    # Largest real root of x^5 - 2x^4 - 7x^3 - 2x + 2 = 0 via Newton.
    def f(x: float) -> float:
        return x**5 - 2.0 * x**4 - 7.0 * x**3 - 2.0 * x + 2.0

    def df(x: float) -> float:
        return 5.0 * x**4 - 8.0 * x**3 - 21.0 * x**2 - 2.0

    x = 3.85
    for _ in range(iters):
        x = x - f(x) / df(x)
    return x


def negative_real_root_mu_minus(iters: int = 80) -> float:
    # Unique negative real root of x^5 - 2x^4 - 7x^3 - 2x + 2 = 0 via Newton.
    def f(x: float) -> float:
        return x**5 - 2.0 * x**4 - 7.0 * x**3 - 2.0 * x + 2.0

    def df(x: float) -> float:
        return 5.0 * x**4 - 8.0 * x**3 - 21.0 * x**2 - 2.0

    x = -1.96
    for _ in range(iters):
        x = x - f(x) / df(x)
    return x


def mertens_tail_bound_A4(k_max: int, r4: float, lambda4: float, k_cap: int = 200000) -> float:
    # Unconditional bound from |log(1-w)| <= |w|/(1-|w|), using |mu1|=r4 and
    # |mu_j|<=lambda4 for j!=1. This bounds:
    #   R_{>K} = Σ_{k>K} μ(k)/k * log ζ_A4(r4^{-k})
    # by a positive series with μ(k) replaced by 1 in absolute value.
    s = 0.0
    for k in range(k_max + 1, k_cap + 1):
        a = r4 ** (1 - k)
        t1 = a / (1.0 - a)
        b = lambda4 / (r4**k)
        t2 = b / (1.0 - b)
        term = (1.0 / float(k)) * (t1 + 4.0 * t2)
        s += term
        if term < 1e-220:
            break
    return s


@dataclass(frozen=True)
class FinitePart:
    r4: float
    lambda4: float
    z_star: float
    C: float
    log_mathfrak_M: float
    mertens_M: float
    k_max: int
    tail_bound: float


def compute_finite_part(k_max: int, tail_tol: float, prog: Progress) -> FinitePart:
    r4 = perron_root_r4()
    mu_minus = negative_real_root_mu_minus()
    lambda4 = abs(mu_minus)
    z_star = 1.0 / r4
    C = 1.0 / (-z_star * delta_prime(z_star))

    mu = mobius_upto(k_max)
    s = 0.0
    last_abs = 0.0
    for k in range(2, k_max + 1):
        if mu[k] == 0:
            continue
        zk = z_star**k
        term = (mu[k] / float(k)) * math.log(zeta(zk))
        s += term
        last_abs = abs(term)
        prog.tick(f"k={k}/{k_max} term={term:.3e} partial={s:.6f} last_abs={last_abs:.3e}")

    log_mathfrak_M = math.log(C) + s
    gamma = 0.577215664901532860606512090082402431  # Euler–Mascheroni
    mertens_M = gamma + log_mathfrak_M

    tail_bound = mertens_tail_bound_A4(k_max=k_max, r4=r4, lambda4=lambda4)
    if tail_bound > tail_tol:
        prog.tick(f"WARNING tail_bound ~ {tail_bound:.3e} > tail_tol {tail_tol:.3e}")

    return FinitePart(
        r4=r4,
        lambda4=lambda4,
        z_star=z_star,
        C=C,
        log_mathfrak_M=log_mathfrak_M,
        mertens_M=mertens_M,
        k_max=k_max,
        tail_bound=tail_bound,
    )


def write_table_tex(path: Path, fp: FinitePart) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Abel/Mertens finite-part constants for the 4th-collision kernel $A_4$. "
        "Here $z_\\star=1/\\rho(A_4)$, $C=\\lim_{z\\to z_\\star}(1-\\rho z)\\zeta_{A_4}(z)$, "
        "$\\log\\mathfrak{M}=\\log C+\\sum_{k\\ge2}\\mu(k)\\log\\zeta_{A_4}(z_\\star^k)/k$, and "
        "$\\mathsf{M}=\\gamma+\\log\\mathfrak{M}$.}"
    )
    lines.append("\\label{tab:collision_kernel_A4_finite_part}")
    lines.append("\\begin{tabular}{r r}")
    lines.append("\\toprule")
    lines.append("Quantity & Value\\\\")
    lines.append("\\midrule")
    lines.append(f"$r_4=\\rho(A_4)$ & {fp.r4:.12f}\\\\")
    lines.append(f"$\\Lambda_4$ & {fp.lambda4:.12f}\\\\")
    lines.append(f"$z_\\star=1/r_4$ & {fp.z_star:.12f}\\\\")
    lines.append(f"$C$ & {fp.C:.12f}\\\\")
    lines.append(f"$\\log\\mathfrak{{M}}$ & {fp.log_mathfrak_M:.12f}\\\\")
    lines.append(f"$\\mathsf{{M}}=\\gamma+\\log\\mathfrak{{M}}$ & {fp.mertens_M:.12f}\\\\")
    lines.append(f"$k_{{\\max}}$ & {fp.k_max}\\\\")
    lines.append(f"tail bound & {fp.tail_bound:.3e}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute Abel/Mertens finite-part for 4th-collision kernel A4.")
    parser.add_argument("--k-max", type=int, default=250, help="Max k for Möbius tail sum.")
    parser.add_argument("--tail-tol", type=float, default=1e-12, help="Target tail tolerance (proxy).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_kernel_A4_finite_part.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_collision_kernel_A4_finite_part.tex"),
        help="Output LaTeX table path.",
    )
    args = parser.parse_args()

    prog = Progress("collision-A4-finite-part", every_seconds=20.0)
    fp = compute_finite_part(k_max=args.k_max, tail_tol=args.tail_tol, prog=prog)

    payload: Dict[str, object] = {
        "k_max": fp.k_max,
        "tail_bound": fp.tail_bound,
        "r4": fp.r4,
        "Lambda4": fp.lambda4,
        "z_star": fp.z_star,
        "C": fp.C,
        "log_mathfrak_M": fp.log_mathfrak_M,
        "mertens_M": fp.mertens_M,
        "delta_poly": [1, -2, -7, 0, -2, 2],
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"[collision-A4-finite-part] wrote {jout}", flush=True)

    write_table_tex(Path(args.tex_out), fp)
    print(f"[collision-A4-finite-part] wrote {args.tex_out}", flush=True)


if __name__ == "__main__":
    main()

