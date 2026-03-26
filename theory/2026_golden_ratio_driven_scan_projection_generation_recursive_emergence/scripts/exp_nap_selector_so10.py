#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Non-Abelian preservation (NAP) selector in Zeckendorf–Fibonacci resolution signatures.

All code is English-only by repository convention.

We use the boundary-word tower dictionary (see exp_boundary_tower_gut_signatures.py):
  - |X_m^{bdry}| = F_{m-2}, with Fibonacci F_1=F_2=1
  - For a Lie algebra g with D=dim g, the Zeckendorf decomposition
        D = sum_{k in S} F_k   (no adjacent indices)
    induces the unique resolution-signature
        Sigma(g) = { k+2 : k in S }  such that  D = sum_{m in Sigma(g)} |X_m^{bdry}|.

NAP constraint (as used in the manuscript text):
  - Treat {6,8} as "non-Abelian resonance layers" that must remain as independent layers
    under a unification jump; i.e. require {6,8} ⊂ Sigma(g).
  - Among all simple Lie algebras, pick the minimal-dimension solution.

We also report a stricter variant requiring {4,6,8} ⊂ Sigma(g).

Outputs:
  - artifacts/export/nap_selector_so10.json
  - sections/generated/tab_nap_selector_so10.tex
  - sections/generated/eq_nap_selector_so10.tex
"""

from __future__ import annotations

import argparse
import json
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

    # Find smallest k_max with F_{k_max} >= D, then greedy downward.
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
        k -= 2  # enforce non-adjacent indices

    # Sanity checks: decreasing and non-adjacent.
    for a, b in zip(picks, picks[1:]):
        if not (a > b + 1):
            raise RuntimeError(f"Adjacent/unsorted Zeckendorf picks for D={D}: {picks}")
    if sum(_fib_value(kk) for kk in picks) != D:
        raise RuntimeError(f"Bad Zeckendorf sum for D={D}: picks={picks}")
    return picks


def sigma_layers_from_zeckendorf(picks: Sequence[int]) -> List[int]:
    """Sigma = {k+2 : k in picks}, returned as descending list."""
    return sorted([int(k) + 2 for k in picks], reverse=True)


def _tex_set_int(xs: Iterable[int]) -> str:
    return "\\{" + ",".join(str(int(x)) for x in xs) + "\\}"


def _tex_zeckendorf_sum(D: int, picks: Sequence[int]) -> str:
    parts = "+".join(f"F_{{{int(k)}}}" for k in picks)
    return f"{int(D)}={parts}"


@dataclass(frozen=True)
class Candidate:
    """A simple Lie algebra candidate with its Zeckendorf signature."""

    family: str
    rank: int
    name_tex: str
    D: int
    zeckendorf_indices: List[int]
    sigma_layers: List[int]


def _classical_candidates(rank_max: int) -> List[Candidate]:
    out: List[Candidate] = []
    nmax = int(rank_max)
    for n in range(1, nmax + 1):
        # A_n: su(n+1), dim = (n+1)^2 - 1
        D_A = int((n + 1) * (n + 1) - 1)
        picks = zeckendorf_decompose(D_A)
        out.append(
            Candidate(
                family="A",
                rank=n,
                name_tex=f"SU({n+1})",
                D=D_A,
                zeckendorf_indices=picks,
                sigma_layers=sigma_layers_from_zeckendorf(picks),
            )
        )

        # B_n: so(2n+1), dim = n(2n+1)
        D_B = int(n * (2 * n + 1))
        picks = zeckendorf_decompose(D_B)
        out.append(
            Candidate(
                family="B",
                rank=n,
                name_tex=f"SO({2*n+1})",
                D=D_B,
                zeckendorf_indices=picks,
                sigma_layers=sigma_layers_from_zeckendorf(picks),
            )
        )

        # C_n: sp(2n), dim = n(2n+1)
        D_C = int(n * (2 * n + 1))
        picks = zeckendorf_decompose(D_C)
        out.append(
            Candidate(
                family="C",
                rank=n,
                name_tex=f"Sp({2*n})",
                D=D_C,
                zeckendorf_indices=picks,
                sigma_layers=sigma_layers_from_zeckendorf(picks),
            )
        )

        # D_n: so(2n), dim = n(2n-1) for n>=2 (D_2 is not simple but we keep it for completeness).
        if n >= 2:
            D_D = int(n * (2 * n - 1))
            picks = zeckendorf_decompose(D_D)
            out.append(
                Candidate(
                    family="D",
                    rank=n,
                    name_tex=f"SO({2*n})",
                    D=D_D,
                    zeckendorf_indices=picks,
                    sigma_layers=sigma_layers_from_zeckendorf(picks),
                )
            )
    return out


def _exceptional_candidates() -> List[Candidate]:
    # Rank and dimensions are standard.
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
        out.append(
            Candidate(
                family=fam,
                rank=int(rk),
                name_tex=name,
                D=int(D),
                zeckendorf_indices=picks,
                sigma_layers=sigma_layers_from_zeckendorf(picks),
            )
        )
    return out


def _filter_by_layers(cands: Sequence[Candidate], required_layers: Set[int]) -> List[Candidate]:
    req = {int(x) for x in required_layers}
    out = [c for c in cands if req.issubset(set(c.sigma_layers))]
    out.sort(key=lambda c: (int(c.D), c.family, int(c.rank), c.name_tex))
    return out


def _write_table_tex(path: Path, *, nap: List[Candidate], strict: List[Candidate], topk: int) -> None:
    topk = int(topk)
    nap_top = nap[: max(1, topk)]
    strict_top = strict[: max(1, topk)]

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_nap_selector_so10.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.12}")
    lines.append(
        "\\caption{Non-Abelian preservation (NAP) selector in Zeckendorf--Fibonacci resolution signatures. "
        "We scan simple Lie algebras (classical families up to a fixed rank cut plus exceptional types), "
        "compute $\\Sigma(\\mathfrak g)$ from the Zeckendorf decomposition of $D=\\dim\\mathfrak g$, "
        "and report the minimal-dimension solutions under the constraints "
        "$\\{6,8\\}\\subseteq\\Sigma(\\mathfrak g)$ (NAP) and $\\{4,6,8\\}\\subseteq\\Sigma(\\mathfrak g)$ (strict).}"
    )
    lines.append("\\label{tab:nap_selector_so10}")
    lines.append("\\begin{tabular}{l l r l l}")
    lines.append("\\toprule")
    lines.append("constraint & $\\mathfrak g$ & $D$ & Zeckendorf & $\\Sigma(\\mathfrak g)$\\\\")
    lines.append("\\midrule")

    def row(constraint_tex: str, c: Candidate) -> str:
        ztex = "$" + _tex_zeckendorf_sum(c.D, c.zeckendorf_indices) + "$"
        stex = "$" + _tex_set_int(c.sigma_layers) + "$"
        return f"{constraint_tex} & ${c.name_tex}$ & {c.D} & {ztex} & {stex}\\\\"

    for i, c in enumerate(nap_top):
        lines.append(row("NAP", c))
        if i == 0 and len(nap_top) > 1:
            # Visual spacer after the minimum.
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


def _write_eq_tex(path: Path) -> None:
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_nap_selector_so10.py")
    lines.append("\\begin{equation}\\label{eq_nap_selector_so10}")
    lines.append("\\begin{aligned}")
    lines.append("\\Sigma_{\\mathrm{SM}}&=\\{4,6,8\\},\\qquad 12=F_6+F_4+F_2=8+3+1,\\\\")
    lines.append("\\Sigma_{SO(10)}&=\\{6,8,11\\},\\qquad 45=F_9+F_6+F_4=34+8+3,\\\\")
    lines.append("\\Sigma_{SO(10)}&=\\Sigma_{\\mathrm{SM}}\\setminus\\{4\\}\\cup\\{11\\},\\\\")
    lines.append(
        "|X_{11}^{\\mathrm{bdry}}|-|X_{4}^{\\mathrm{bdry}}|"
        "&=F_9-F_2=34-1=33\\\\"
    )
    lines.append("&=45-12.")
    lines.append("\\end{aligned}")
    lines.append("\\end{equation}")
    lines.append("")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="NAP selector in Zeckendorf resolution signatures (find minimal SO(10)).")
    ap.add_argument("--rank-max", type=int, default=64, help="Max rank for classical families A/B/C/D.")
    ap.add_argument("--topk", type=int, default=10, help="How many candidates to show per constraint.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "nap_selector_so10.json"),
    )
    ap.add_argument(
        "--tex-tab",
        type=str,
        default=str(generated_dir() / "tab_nap_selector_so10.tex"),
    )
    ap.add_argument(
        "--tex-eq",
        type=str,
        default=str(generated_dir() / "eq_nap_selector_so10.tex"),
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

    # Prepare JSON (audit).
    payload: Dict[str, object] = {
        "params": {
            "rank_max": rank_max,
            "nap_required_layers": sorted(list(required_nap)),
            "strict_required_layers": sorted(list(required_strict)),
            "topk": topk,
        },
        "min_nap": asdict(nap[0]),
        "min_strict": asdict(strict[0]),
        "top_nap": [asdict(c) for c in nap[:topk]],
        "top_strict": [asdict(c) for c in strict[:topk]],
    }

    json_out = Path(args.json_out)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    _write_table_tex(Path(args.tex_tab), nap=nap, strict=strict, topk=topk)
    _write_eq_tex(Path(args.tex_eq))

    print(f"[nap-selector] wrote {args.tex_tab}", flush=True)
    print(f"[nap-selector] wrote {args.tex_eq}", flush=True)
    print(f"[nap-selector] wrote {args.json_out}", flush=True)


if __name__ == "__main__":
    main()

