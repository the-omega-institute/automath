#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Information-cost selector Omega(g) on Zeckendorf--Fibonacci resolution signatures.

All code is English-only by repository convention.

Manuscript context:
  - The Zeckendorf--GUT dictionary assigns each simple Lie algebra g a unique
    resolution signature Sigma(g) (layer set) derived from the Zeckendorf
    decomposition of D=dim g in Fibonacci numbers.
  - Independently, the dyadic fold at resolution m has average multiplicity
        d_m := 2^m / |X_m| = 2^m / F_{m+2}.
    This can be interpreted as an information / compression cost per active layer.

We define an additive information-cost functional
    Omega(g) := sum_{m in Sigma(g)} log d_m,
and compute the minimal Omega solution under the same constraints used by the
NAP selector in the manuscript:
  - NAP: require {6,8} ⊂ Sigma(g)
  - strict: require {4,6,8} ⊂ Sigma(g)

Outputs:
  - artifacts/export/gut_information_cost_selector.json
  - sections/generated/tab_gut_information_cost_selector.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Set, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import fib_upto


def _fib_value(k: int) -> int:
    """Return Fibonacci number F_k with F_1=F_2=1 (k>=1)."""
    if k <= 0:
        raise ValueError("k must be >= 1")
    return int(fib_upto(int(k))[-1])


def zeckendorf_decompose(D: int) -> List[int]:
    """Return Zeckendorf indices S such that D = sum_{k in S} F_k (k>=2, no adjacent)."""
    if D < 0:
        raise ValueError("D must be non-negative")
    if D == 0:
        return []

    k_max = 2
    while _fib_value(k_max) < D:
        k_max += 1

    rem = int(D)
    picks: List[int] = []
    k = int(k_max)
    while rem > 0:
        while k >= 2 and _fib_value(k) > rem:
            k -= 1
        if k < 2:
            raise RuntimeError(f"Zeckendorf decomposition failed for D={D} (rem={rem})")
        picks.append(int(k))
        rem -= _fib_value(k)
        k -= 2

    for a, b in zip(picks, picks[1:]):
        if not (a > b + 1):
            raise RuntimeError(f"Adjacent/unsorted Zeckendorf picks for D={D}: {picks}")
    if sum(_fib_value(kk) for kk in picks) != D:
        raise RuntimeError(f"Bad Zeckendorf sum for D={D}: picks={picks}")
    return picks


def sigma_layers_from_zeckendorf(picks: Sequence[int]) -> List[int]:
    """Sigma = {k+2 : k in picks}, returned as descending list."""
    return sorted([int(k) + 2 for k in picks], reverse=True)


def d_fold(m: int) -> float:
    """Average dyadic fold multiplicity d_m = 2^m / F_{m+2} (F_1=F_2=1)."""
    if m < 0:
        raise ValueError("m must be non-negative")
    denom = _fib_value(int(m) + 2)
    return float((1 << int(m)) / denom)


def omega_of_sigma(sigma_layers: Sequence[int]) -> float:
    return float(sum(math.log(d_fold(int(m))) for m in sigma_layers))


def _tex_set_int(xs: Iterable[int]) -> str:
    return "\\{" + ",".join(str(int(x)) for x in xs) + "\\}"


@dataclass(frozen=True)
class Candidate:
    family: str
    rank: int
    name_tex: str
    D: int
    zeckendorf_indices: List[int]
    sigma_layers: List[int]
    omega: float


def _classical_candidates(rank_max: int) -> List[Candidate]:
    out: List[Candidate] = []
    nmax = int(rank_max)
    for n in range(1, nmax + 1):
        # A_n: su(n+1), dim=(n+1)^2-1
        D_A = int((n + 1) * (n + 1) - 1)
        picks = zeckendorf_decompose(D_A)
        sigma = sigma_layers_from_zeckendorf(picks)
        out.append(
            Candidate(
                family="A",
                rank=int(n),
                name_tex=f"SU({n+1})",
                D=int(D_A),
                zeckendorf_indices=picks,
                sigma_layers=sigma,
                omega=omega_of_sigma(sigma),
            )
        )

        # B_n: so(2n+1), dim=n(2n+1)
        D_B = int(n * (2 * n + 1))
        picks = zeckendorf_decompose(D_B)
        sigma = sigma_layers_from_zeckendorf(picks)
        out.append(
            Candidate(
                family="B",
                rank=int(n),
                name_tex=f"SO({2*n+1})",
                D=int(D_B),
                zeckendorf_indices=picks,
                sigma_layers=sigma,
                omega=omega_of_sigma(sigma),
            )
        )

        # C_n: sp(2n), dim=n(2n+1)
        D_C = int(n * (2 * n + 1))
        picks = zeckendorf_decompose(D_C)
        sigma = sigma_layers_from_zeckendorf(picks)
        out.append(
            Candidate(
                family="C",
                rank=int(n),
                name_tex=f"Sp({2*n})",
                D=int(D_C),
                zeckendorf_indices=picks,
                sigma_layers=sigma,
                omega=omega_of_sigma(sigma),
            )
        )

        # D_n: so(2n), dim=n(2n-1) for n>=2.
        if n >= 2:
            D_D = int(n * (2 * n - 1))
            picks = zeckendorf_decompose(D_D)
            sigma = sigma_layers_from_zeckendorf(picks)
            out.append(
                Candidate(
                    family="D",
                    rank=int(n),
                    name_tex=f"SO({2*n})",
                    D=int(D_D),
                    zeckendorf_indices=picks,
                    sigma_layers=sigma,
                    omega=omega_of_sigma(sigma),
                )
            )
    return out


def _exceptional_candidates() -> List[Candidate]:
    exc: List[Tuple[str, int, str, int]] = [
        ("G", 2, "G_2", 14),
        ("F", 4, "F_4", 52),
        ("E", 6, "E_6", 78),
        ("E", 7, "E_7", 133),
        ("E", 8, "E_8", 248),
    ]
    out: List[Candidate] = []
    for fam, rk, name, D in exc:
        picks = zeckendorf_decompose(int(D))
        sigma = sigma_layers_from_zeckendorf(picks)
        out.append(
            Candidate(
                family=fam,
                rank=int(rk),
                name_tex=name,
                D=int(D),
                zeckendorf_indices=picks,
                sigma_layers=sigma,
                omega=omega_of_sigma(sigma),
            )
        )
    return out


def _filter_by_layers(cands: Sequence[Candidate], required_layers: Set[int]) -> List[Candidate]:
    req = {int(x) for x in required_layers}
    out = [c for c in cands if req.issubset(set(c.sigma_layers))]
    out.sort(key=lambda c: (float(c.omega), int(c.D), c.family, int(c.rank), c.name_tex))
    return out


def _write_table_tex(path: Path, *, nap: List[Candidate], strict: List[Candidate], topk: int) -> None:
    topk = int(topk)
    nap_top = nap[: max(1, topk)]
    strict_top = strict[: max(1, topk)]

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_gut_information_cost_selector.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.12}")
    lines.append(
        "\\caption{Information-cost selector $\\Omega(\\mathfrak g)=\\sum_{m\\in\\Sigma(\\mathfrak g)}\\log d_m$ "
        "with $d_m:=2^m/F_{m+2}$ (average dyadic-fold multiplicity). "
        "We report the minimal-$\\Omega$ solutions under the same layer constraints used by the NAP selector: "
        "$\\{6,8\\}\\subseteq\\Sigma(\\mathfrak g)$ (NAP) and $\\{4,6,8\\}\\subseteq\\Sigma(\\mathfrak g)$ (strict).}"
    )
    lines.append("\\label{tab:gut_information_cost_selector}")
    lines.append("\\begin{tabular}{l l r l r}")
    lines.append("\\toprule")
    lines.append("constraint & $\\mathfrak g$ & $D$ & $\\Sigma(\\mathfrak g)$ & $\\Omega(\\mathfrak g)$\\\\")
    lines.append("\\midrule")

    def row(constraint_tex: str, c: Candidate) -> str:
        stex = "$" + _tex_set_int(c.sigma_layers) + "$"
        return f"{constraint_tex} & ${c.name_tex}$ & {c.D} & {stex} & {c.omega:.3f}\\\\"

    for i, c in enumerate(nap_top):
        lines.append(row("NAP", c))
        if i == 0 and len(nap_top) > 1:
            lines.append("\\addlinespace[1pt]")

    lines.append("\\midrule")
    for i, c in enumerate(strict_top):
        lines.append(row("strict", c))
        if i == 0 and len(strict_top) > 1:
            lines.append("\\addlinespace[1pt]")

    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Information-cost selector Omega on Zeckendorf resolution signatures.")
    ap.add_argument("--rank-max", type=int, default=64, help="Max rank for classical families A/B/C/D.")
    ap.add_argument("--topk", type=int, default=10, help="How many candidates to show per constraint.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "gut_information_cost_selector.json"),
    )
    ap.add_argument(
        "--tex-tab",
        type=str,
        default=str(generated_dir() / "tab_gut_information_cost_selector.tex"),
    )
    args = ap.parse_args()

    rank_max = int(args.rank_max)
    if rank_max < 1:
        raise SystemExit("--rank-max must be >= 1")
    topk = int(args.topk)
    if topk < 1:
        raise SystemExit("--topk must be >= 1")

    required_nap = {6, 8}
    required_strict = {4, 6, 8}

    cands = [*_classical_candidates(rank_max), *_exceptional_candidates()]
    nap = _filter_by_layers(cands, required_layers=required_nap)
    strict = _filter_by_layers(cands, required_layers=required_strict)
    if not nap:
        raise RuntimeError("No NAP candidates found (unexpected). Increase --rank-max?")
    if not strict:
        raise RuntimeError("No strict candidates found (unexpected). Increase --rank-max?")

    payload: Dict[str, object] = {
        "params": {
            "rank_max": rank_max,
            "topk": topk,
            "definition": {"d_m": "2^m/F_{m+2}", "Omega": "sum_{m in Sigma} log d_m"},
            "nap_required_layers": sorted(list(required_nap)),
            "strict_required_layers": sorted(list(required_strict)),
        },
        "min_nap_by_omega": asdict(nap[0]),
        "min_strict_by_omega": asdict(strict[0]),
        "top_nap_by_omega": [asdict(c) for c in nap[:topk]],
        "top_strict_by_omega": [asdict(c) for c in strict[:topk]],
    }
    json_out = Path(args.json_out)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    _write_table_tex(Path(args.tex_tab), nap=nap, strict=strict, topk=topk)

    print(f"[gut-omega-selector] wrote {args.json_out}", flush=True)
    print(f"[gut-omega-selector] wrote {args.tex_tab}", flush=True)


if __name__ == "__main__":
    main()

