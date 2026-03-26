#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Abel/Mertens finite-part constants for the collision kernel A2.

We treat the 3-state collision kernel A2 as an SFT adjacency matrix and compute
the Abel/Hadamard finite-part constant log 𝔐 (mathfrak M) and the orbit-Mertens
constant 𝕄 = γ + log 𝔐, using the universal formula:

  log 𝔐 = log C + Σ_{k>=2} μ(k)/k * log ζ(z_*^k),

where:
  - ζ(z) = 1/det(I - z A2),
  - z_* = 1/ρ(A2) is the main pole,
  - C = lim_{z->z_*} (1 - ρ z) ζ(z) = 1/(-z_* Δ'(z_*)), Δ(z)=det(I-zA2).

Outputs (default):
  - artifacts/export/collision_kernel_A2_finite_part.json
  - sections/generated/tab_collision_kernel_A2_finite_part.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


def det_delta(z: float) -> float:
    # Δ(z)=det(I - z A2) = 1 - 2z - 2z^2 + 2z^3
    return 1.0 - 2.0 * z - 2.0 * z * z + 2.0 * z * z * z


def det_delta_prime(z: float) -> float:
    # Δ'(z) = -2 - 4z + 6z^2
    return -2.0 - 4.0 * z + 6.0 * z * z


def zeta(z: float) -> float:
    return 1.0 / det_delta(z)


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


def perron_root_r2(iters: int = 40) -> float:
    # Largest real root of x^3 - 2x^2 - 2x + 2 = 0 via Newton.
    def f(x: float) -> float:
        return x**3 - 2.0 * x**2 - 2.0 * x + 2.0

    def df(x: float) -> float:
        return 3.0 * x**2 - 4.0 * x - 2.0

    x = 2.5
    for _ in range(iters):
        x = x - f(x) / df(x)
    return x


@dataclass(frozen=True)
class FinitePart:
    r2: float
    z_star: float
    C: float
    log_mathfrak_M: float
    mertens_M: float
    k_max: int
    tail_bound: float


def compute_finite_part(k_max: int, tail_tol: float, prog: Progress) -> FinitePart:
    r2 = perron_root_r2()
    z_star = 1.0 / r2
    # C = 1/(-z_* Δ'(z_*))
    C = 1.0 / (-z_star * det_delta_prime(z_star))

    mu = mobius_upto(k_max)
    s = 0.0
    # Track a crude tail bound from the last term magnitude.
    last_abs = 0.0
    for k in range(2, k_max + 1):
        if mu[k] == 0:
            continue
        zk = z_star**k
        term = (mu[k] / float(k)) * math.log(zeta(zk))
        s += term
        last_abs = abs(term)
        prog.tick(f"k={k}/{k_max} term={term:.3e} partial={s:.6f}")

    log_mathfrak_M = math.log(C) + s
    gamma = 0.577215664901532860606512090082402431  # Euler–Mascheroni
    mertens_M = gamma + log_mathfrak_M

    # For z_star^k small, log zeta(z_star^k) ~ 2 z_star^k (since Δ(z)=1-2z+O(z^2)).
    # So a naive tail proxy is O(z_star^(k_max+1)).
    tail_bound = 10.0 * (z_star ** (k_max + 1))
    if tail_bound > tail_tol:
        prog.tick(f"WARNING tail_bound ~ {tail_bound:.3e} > tail_tol {tail_tol:.3e}")

    return FinitePart(
        r2=r2,
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
        "\\caption{Abel/Mertens finite-part constants for the collision kernel $A_2$. "
        "Here $z_\\star=1/\\rho(A_2)$, $C=\\lim_{z\\to z_\\star}(1-\\rho z)\\zeta_{A_2}(z)$, "
        "$\\log\\mathfrak{M}=\\log C+\\sum_{k\\ge2}\\mu(k)\\log\\zeta_{A_2}(z_\\star^k)/k$, and "
        "$\\mathsf{M}=\\gamma+\\log\\mathfrak{M}$.}"
    )
    lines.append("\\label{tab:collision_kernel_A2_finite_part}")
    lines.append("\\begin{tabular}{r r}")
    lines.append("\\toprule")
    lines.append("Quantity & Value\\\\")
    lines.append("\\midrule")
    lines.append(f"$r_2=\\rho(A_2)$ & {fp.r2:.12f}\\\\")
    lines.append(f"$z_\\star=1/r_2$ & {fp.z_star:.12f}\\\\")
    lines.append(f"$C$ & {fp.C:.12f}\\\\")
    lines.append(f"$\\log\\mathfrak{{M}}$ & {fp.log_mathfrak_M:.12f}\\\\")
    lines.append(f"$\\mathsf{{M}}=\\gamma+\\log\\mathfrak{{M}}$ & {fp.mertens_M:.12f}\\\\")
    lines.append(f"$k_{{\\max}}$ & {fp.k_max}\\\\")
    lines.append(f"tail proxy & {fp.tail_bound:.3e}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute Abel/Mertens finite-part for collision kernel A2.")
    parser.add_argument("--k-max", type=int, default=200, help="Max k for Möbius tail sum.")
    parser.add_argument("--tail-tol", type=float, default=1e-12, help="Target tail tolerance (proxy).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_kernel_A2_finite_part.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_collision_kernel_A2_finite_part.tex"),
        help="Output LaTeX table path.",
    )
    args = parser.parse_args()

    prog = Progress("collision-A2-finite-part", every_seconds=20.0)
    fp = compute_finite_part(k_max=args.k_max, tail_tol=args.tail_tol, prog=prog)

    payload: Dict[str, object] = {
        "k_max": fp.k_max,
        "tail_proxy": fp.tail_bound,
        "r2": fp.r2,
        "z_star": fp.z_star,
        "C": fp.C,
        "log_mathfrak_M": fp.log_mathfrak_M,
        "mertens_M": fp.mertens_M,
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"[collision-A2-finite-part] wrote {jout}", flush=True)

    write_table_tex(Path(args.tex_out), fp)
    print(f"[collision-A2-finite-part] wrote {args.tex_out}", flush=True)


if __name__ == "__main__":
    main()

