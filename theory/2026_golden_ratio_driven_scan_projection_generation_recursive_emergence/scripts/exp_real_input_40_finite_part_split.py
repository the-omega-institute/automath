#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Finite-part constants for the real-input 40-state kernel, with zeta factor split.

We use the exact determinant factorization (paper):
  det(I - z M)
    = (1-z)^2 (1+z)^3 (1-3z+z^2) (1+z-z^2).

and the structural split (also in the paper):
  det(I - z M)
    = det_triv(z) * det_in(z) * det_twist(z),
  det_triv(z) = (1-z)^2 (1+z),
  det_in(z)   = det(I - z(A⊗A)) = (1+z)^2 (1-3z+z^2),
  det_twist(z)= det(I + z A)     = (1+z-z^2),
where A=[[1,1],[1,0]] is the golden-mean skeleton matrix.

Thus:
  ζ_M(z) = ζ_in(z) * ζ_twist(z) * ζ_triv(z),
with:
  ζ_in(z)   = 1/det_in(z),
  ζ_twist(z)= 1/det_twist(z),
  ζ_triv(z) = 1/det_triv(z).

The main pole is at z_* = 1/λ = φ^{-2}, coming from (1-3z+z^2)=0.
Only ζ_in has the simple pole at z_*. The other factors are analytic at z_*.

We compute:
  log 𝔐_total (for ζ_M),
  log 𝔐_in    (for ζ_in),
and define analytic-factor contributions (additive on log-scale):
  log 𝔐_factor := log f(z_*) + Σ_{k>=2} μ(k)/k log f(z_*^k),
for f=ζ_twist, ζ_triv.
Then:
  log 𝔐_total = log 𝔐_in + log 𝔐_twist + log 𝔐_triv.

Outputs:
  - artifacts/export/real_input_40_finite_part_split.json
  - sections/generated/tab_real_input_40_finite_part_split.tex

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
from common_phi_fold import PHI, Progress


def det_triv(z: float) -> float:
    return (1.0 - z) ** 2 * (1.0 + z)


def det_in(z: float) -> float:
    # det(I - z(A⊗A)) = (1+z)^2(1-3z+z^2)
    return (1.0 + z) ** 2 * (1.0 - 3.0 * z + z * z)


def det_twist(z: float) -> float:
    # det(I + z A) = 1 + z - z^2
    return 1.0 + z - z * z


def det_total(z: float) -> float:
    # det(I - z M) = (1-z)^2 (1+z)^3 (1-3z+z^2) (1+z-z^2)
    return (1.0 - z) ** 2 * (1.0 + z) ** 3 * (1.0 - 3.0 * z + z * z) * (1.0 + z - z * z)


def det_in_prime(z: float) -> float:
    # derivative of det_in(z) = (1+z)^2(1-3z+z^2)
    # = (1+z)^2 * q(z), q=1-3z+z^2
    # d = 2(1+z)q + (1+z)^2 q'
    q = 1.0 - 3.0 * z + z * z
    qp = -3.0 + 2.0 * z
    return 2.0 * (1.0 + z) * q + (1.0 + z) ** 2 * qp


def zeta_triv(z: float) -> float:
    return 1.0 / det_triv(z)


def zeta_in(z: float) -> float:
    return 1.0 / det_in(z)


def zeta_twist(z: float) -> float:
    return 1.0 / det_twist(z)


def zeta_total(z: float) -> float:
    return 1.0 / det_total(z)


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


@dataclass(frozen=True)
class SplitFinitePart:
    lam: float
    z_star: float
    z_star_exact: str
    C_in: float
    C_total: float
    C_in_exact: str
    C_total_exact: str
    zeta_triv_at_z_star: float
    zeta_twist_at_z_star: float
    zeta_triv_at_z_star_exact: str
    zeta_twist_at_z_star_exact: str
    logM_in: float
    logM_twist: float
    logM_triv: float
    logM_total: float
    mertens_in: float
    mertens_total: float
    k_max: int
    tail_proxy: float
    consistency_err: float


def compute_split(k_max: int, tail_tol: float, prog: Progress) -> SplitFinitePart:
    phi = PHI
    lam = phi * phi
    z_star = 1.0 / lam
    z_star_exact = r"$(3-\sqrt{5})/2$"

    # Residue constant for ζ_in at z_star: C_in = 1/(-z_star * det_in'(z_star)).
    C_in = 1.0 / (-z_star * det_in_prime(z_star))
    C_in_exact = r"$3/10+7\sqrt{5}/50$"

    # Since ζ_total = ζ_in * ζ_twist * ζ_triv and only ζ_in has the pole,
    # residue multiplies by analytic factors at z_star.
    zeta_triv_at_z_star = zeta_triv(z_star)
    zeta_twist_at_z_star = zeta_twist(z_star)
    C_total = C_in * zeta_twist_at_z_star * zeta_triv_at_z_star
    zeta_triv_at_z_star_exact = r"$1+2\sqrt{5}/5$"
    zeta_twist_at_z_star_exact = r"$(1+\sqrt{5})/4$"
    C_total_exact = r"$(47+21\sqrt{5})/100$"

    mu = mobius_upto(k_max)
    s_in = 0.0
    s_twist = 0.0
    s_triv = 0.0
    last_abs = 0.0
    for k in range(2, k_max + 1):
        if mu[k] == 0:
            continue
        zk = z_star**k
        term_in = (mu[k] / float(k)) * math.log(zeta_in(zk))
        term_tw = (mu[k] / float(k)) * math.log(zeta_twist(zk))
        term_tr = (mu[k] / float(k)) * math.log(zeta_triv(zk))
        s_in += term_in
        s_twist += term_tw
        s_triv += term_tr
        last_abs = max(last_abs, abs(term_in) + abs(term_tw) + abs(term_tr))
        prog.tick(
            f"k={k}/{k_max} partial_in={s_in:.6f} partial_tw={s_twist:.6f} partial_tr={s_triv:.6f}"
        )

    # Analytic-factor contributions include the k=1 evaluation at z_star (as log f(z_star)).
    logM_in = math.log(C_in) + s_in
    logM_twist = math.log(zeta_twist(z_star)) + s_twist
    logM_triv = math.log(zeta_triv(z_star)) + s_triv
    logM_total = math.log(C_total) + (s_in + s_twist + s_triv)

    gamma = 0.577215664901532860606512090082402431  # Euler–Mascheroni
    mertens_in = gamma + logM_in
    mertens_total = gamma + logM_total

    # Tail proxy: z_star^(k_max+1) is tiny; keep a conservative proxy.
    tail_proxy = 10.0 * (z_star ** (k_max + 1))
    if tail_proxy > tail_tol:
        prog.tick(f"WARNING tail_proxy ~ {tail_proxy:.3e} > tail_tol {tail_tol:.3e}")

    # Consistency: logM_total should equal logM_in + logM_twist + logM_triv.
    consistency_err = abs(logM_total - (logM_in + logM_twist + logM_triv))

    return SplitFinitePart(
        lam=lam,
        z_star=z_star,
        z_star_exact=z_star_exact,
        C_in=C_in,
        C_total=C_total,
        C_in_exact=C_in_exact,
        C_total_exact=C_total_exact,
        zeta_triv_at_z_star=zeta_triv_at_z_star,
        zeta_twist_at_z_star=zeta_twist_at_z_star,
        zeta_triv_at_z_star_exact=zeta_triv_at_z_star_exact,
        zeta_twist_at_z_star_exact=zeta_twist_at_z_star_exact,
        logM_in=logM_in,
        logM_twist=logM_twist,
        logM_triv=logM_triv,
        logM_total=logM_total,
        mertens_in=mertens_in,
        mertens_total=mertens_total,
        k_max=k_max,
        tail_proxy=tail_proxy,
        consistency_err=consistency_err,
    )


def write_table_tex(path: Path, fp: SplitFinitePart) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Finite-part split for the real-input 40-state kernel via the exact $\\zeta$-factorization. "
        "We write $\\zeta_M=\\zeta_{\\mathrm{in}}\\,\\zeta_{\\mathrm{twist}}\\,\\zeta_{\\mathrm{triv}}$ at the main pole "
        "$z_\\star=1/\\lambda$ with $\\lambda=\\varphi^2$. The pole belongs to $\\zeta_{\\mathrm{in}}$ only, hence "
        "$C_{\\mathrm{tot}}=C_{\\mathrm{in}}\\,\\zeta_{\\mathrm{twist}}(z_\\star)\\,\\zeta_{\\mathrm{triv}}(z_\\star)$ and "
        "$\\log\\mathfrak{M}_{\\mathrm{tot}}=\\log\\mathfrak{M}_{\\mathrm{in}}+\\log\\mathfrak{M}_{\\mathrm{twist}}+\\log\\mathfrak{M}_{\\mathrm{triv}}$.}"
    )
    lines.append("\\label{tab:real_input_40_finite_part_split}")
    lines.append("\\begin{tabular}{l r}")
    lines.append("\\toprule")
    lines.append("Quantity & Value\\\\")
    lines.append("\\midrule")
    lines.append(r"$\lambda$ & %.12f\\\\" % fp.lam)
    lines.append(r"$z_\star=1/\lambda$ & %.12f\\\\" % fp.z_star)
    lines.append(r"$z_\star$ (exact) & %s\\\\" % fp.z_star_exact)
    lines.append(r"$C_{\mathrm{in}}$ & %.12f\\\\" % fp.C_in)
    lines.append(r"$C_{\mathrm{in}}$ (exact) & %s\\\\" % fp.C_in_exact)
    lines.append(r"$C_{\mathrm{tot}}$ & %.12f\\\\" % fp.C_total)
    lines.append(r"$C_{\mathrm{tot}}$ (exact) & %s\\\\" % fp.C_total_exact)
    lines.append(r"$\zeta_{\mathrm{triv}}(z_\star)$ & %.12f\\\\" % fp.zeta_triv_at_z_star)
    lines.append(r"$\zeta_{\mathrm{triv}}(z_\star)$ (exact) & %s\\\\" % fp.zeta_triv_at_z_star_exact)
    lines.append(r"$\zeta_{\mathrm{twist}}(z_\star)$ & %.12f\\\\" % fp.zeta_twist_at_z_star)
    lines.append(r"$\zeta_{\mathrm{twist}}(z_\star)$ (exact) & %s\\\\" % fp.zeta_twist_at_z_star_exact)
    lines.append(r"$\log\mathfrak{M}_{\mathrm{in}}$ & %.12f\\\\" % fp.logM_in)
    lines.append(r"$\log\mathfrak{M}_{\mathrm{twist}}$ & %.12f\\\\" % fp.logM_twist)
    lines.append(r"$\log\mathfrak{M}_{\mathrm{triv}}$ & %.12f\\\\" % fp.logM_triv)
    lines.append(r"$\log\mathfrak{M}_{\mathrm{tot}}$ & %.12f\\\\" % fp.logM_total)
    lines.append(r"$\mathsf{M}_{\mathrm{in}}=\gamma+\log\mathfrak{M}_{\mathrm{in}}$ & %.12f\\\\" % fp.mertens_in)
    lines.append(r"$\mathsf{M}_{\mathrm{tot}}=\gamma+\log\mathfrak{M}_{\mathrm{tot}}$ & %.12f\\\\" % fp.mertens_total)
    lines.append(r"$k_{\max}$ & %d\\\\" % fp.k_max)
    lines.append("tail proxy & %.3e\\\\"
                 % fp.tail_proxy)
    lines.append("consistency err & %.3e\\\\"
                 % fp.consistency_err)
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute finite-part split for real-input 40-state kernel.")
    parser.add_argument("--k-max", type=int, default=400, help="Max k for Möbius tail sum.")
    parser.add_argument("--tail-tol", type=float, default=1e-14, help="Target tail tolerance (proxy).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_finite_part_split.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_finite_part_split.tex"),
        help="Output LaTeX table path.",
    )
    args = parser.parse_args()

    prog = Progress("real-input-40-fp-split", every_seconds=20.0)
    fp = compute_split(k_max=args.k_max, tail_tol=args.tail_tol, prog=prog)

    payload: Dict[str, object] = {
        "k_max": fp.k_max,
        "tail_proxy": fp.tail_proxy,
        "lambda": fp.lam,
        "z_star": fp.z_star,
        "z_star_exact": fp.z_star_exact,
        "C_in": fp.C_in,
        "C_total": fp.C_total,
        "C_in_exact": fp.C_in_exact,
        "C_total_exact": fp.C_total_exact,
        "zeta_triv_at_z_star": fp.zeta_triv_at_z_star,
        "zeta_twist_at_z_star": fp.zeta_twist_at_z_star,
        "zeta_triv_at_z_star_exact": fp.zeta_triv_at_z_star_exact,
        "zeta_twist_at_z_star_exact": fp.zeta_twist_at_z_star_exact,
        "logM_in": fp.logM_in,
        "logM_twist": fp.logM_twist,
        "logM_triv": fp.logM_triv,
        "logM_total": fp.logM_total,
        "M_in": fp.mertens_in,
        "M_total": fp.mertens_total,
        "consistency_err": fp.consistency_err,
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"[real-input-40-fp-split] wrote {jout}", flush=True)

    write_table_tex(Path(args.tex_out), fp)
    print(f"[real-input-40-fp-split] wrote {args.tex_out}", flush=True)


if __name__ == "__main__":
    main()

