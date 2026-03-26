#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Boundary-word tower and Zeckendorf--Fibonacci GUT signatures.

This script is English-only by repository convention.

We treat the "boundary sector" at resolution m as the endpoint-(1,1) fiber
inside the golden-mean admissible language:
  X_m^{bdry} := { u in X_m : u_1 = 1 and u_m = 1 }.
Then |X_m^{bdry}| = F_{m-2}.

This yields two compact, auditable outputs used in the manuscript:
  (A) SM gauge-boson count 12 as a 3-layer boundary tower:
        |X_4^{bdry}| + |X_6^{bdry}| + |X_8^{bdry}| = 1 + 3 + 8 = 12,
      together with an explicit list of X_8^{bdry}.
  (B) A Zeckendorf dictionary mapping a Lie algebra dimension D to a unique
      set of resolution layers Sigma(D) such that
        D = sum_{m in Sigma(D)} |X_m^{bdry}|.

Outputs:
  - artifacts/export/boundary_tower_gut_signatures.json
  - sections/generated/eq_boundary_tower_sm12.tex
  - sections/generated/tab_zeckendorf_gut_signatures.tex
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import fib_upto, word_to_str


def _golden_words(m: int) -> List[List[int]]:
    """All length-m binary words with no adjacent ones (golden mean SFT)."""
    if m < 0:
        raise ValueError("m must be non-negative")
    out: List[List[int]] = []

    def rec(pos: int, prev1: int, acc: List[int]) -> None:
        if pos == m:
            out.append(list(acc))
            return
        # choose 0
        acc.append(0)
        rec(pos + 1, 0, acc)
        acc.pop()
        # choose 1 if previous was 0
        if prev1 == 0:
            acc.append(1)
            rec(pos + 1, 1, acc)
            acc.pop()

    rec(0, 0, [])
    return out


def boundary_words(m: int) -> List[str]:
    """Return X_m^{bdry} as a sorted list of bitstrings."""
    if m <= 0:
        return []
    words = [w for w in _golden_words(m) if w[0] == 1 and w[-1] == 1]
    s = sorted(word_to_str(w) for w in words)
    return s


def _fib_value(k: int) -> int:
    """Return Fibonacci number F_k with F_1=F_2=1 (k>=1)."""
    if k <= 0:
        raise ValueError("k must be >= 1")
    return fib_upto(k)[-1]


def zeckendorf_decompose(D: int) -> List[int]:
    """Return Zeckendorf indices S such that D = sum_{k in S} F_k (k>=2, no adjacent)."""
    if D < 0:
        raise ValueError("D must be non-negative")
    if D == 0:
        return []

    # Build Fibonacci numbers up to >= D.
    k_max = 2
    while _fib_value(k_max) < D:
        k_max += 1

    rem = D
    picks: List[int] = []
    k = k_max
    while rem > 0:
        # Find largest allowed Fibonacci <= rem, with k>=2 (Zeckendorf convention).
        while k >= 2 and _fib_value(k) > rem:
            k -= 1
        if k < 2:
            raise RuntimeError(f"Zeckendorf decomposition failed for D={D} (rem={rem})")
        picks.append(k)
        rem -= _fib_value(k)
        k -= 2  # enforce non-adjacent indices

    # Sanity checks: strictly decreasing indices and non-adjacent.
    for a, b in zip(picks, picks[1:]):
        if not (a > b + 1):
            raise RuntimeError(f"Adjacent/unsorted Zeckendorf picks for D={D}: {picks}")
    if sum(_fib_value(kk) for kk in picks) != D:
        raise RuntimeError(f"Bad Zeckendorf sum for D={D}: picks={picks}")

    return picks


def _tex_set_int(xs: List[int]) -> str:
    return "\\{" + ",".join(str(x) for x in xs) + "\\}"


def _tex_zeckendorf_sum(D: int, picks: List[int]) -> str:
    # Example: "12=F_6+F_4+F_2"
    parts = "+".join(f"F_{{{k}}}" for k in picks)
    return f"{D}={parts}"


@dataclass(frozen=True)
class Candidate:
    name_tex: str
    D: int


def write_outputs(*, tex_eq: Path, tex_tab: Path, json_out: Path) -> None:
    # Boundary tower (explicit sets for small m).
    bdry4 = boundary_words(4)
    bdry6 = boundary_words(6)
    bdry8 = boundary_words(8)

    # Expected counts |X_m^{bdry}| = F_{m-2}.
    assert len(bdry4) == _fib_value(2)  # F_2=1
    assert len(bdry6) == _fib_value(4)  # F_4=3
    assert len(bdry8) == _fib_value(6)  # F_6=8

    # Zeckendorf-GUT dictionary examples (dimension = number of gauge bosons).
    cands: List[Candidate] = [
        Candidate(name_tex="\\mathfrak{g}_{\\mathrm{SM}}", D=12),
        Candidate(name_tex="SU(5)", D=24),
        Candidate(name_tex="SO(10)", D=45),
        Candidate(name_tex="E_6", D=78),
        Candidate(name_tex="E_7", D=133),
        Candidate(name_tex="E_8", D=248),
    ]

    rows: List[Dict[str, object]] = []
    for c in cands:
        picks = zeckendorf_decompose(c.D)
        sigma = [k + 2 for k in picks]  # since |X_m^{bdry}|=F_{m-2}
        rows.append(
            {
                "name_tex": c.name_tex,
                "D": c.D,
                "zeckendorf_indices": picks,
                "zeckendorf_values": [_fib_value(k) for k in picks],
                "sigma_layers": sigma,
            }
        )

    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(
        json.dumps(
            {
                "boundary_sets": {"m4": bdry4, "m6": bdry6, "m8": bdry8},
                "candidates": rows,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    # --- LaTeX equation fragment (SM 12 as a 3-layer boundary tower) ---
    eq_lines: List[str] = []
    eq_lines.append("% AUTO-GENERATED by scripts/exp_boundary_tower_gut_signatures.py")
    eq_lines.append("\\[")
    eq_lines.append("\\begin{aligned}")
    eq_lines.append(
        "|X^{\\mathrm{bdry}}_4|"
        " &= F_2 = 1,\\qquad X^{\\mathrm{bdry}}_4=\\{\\texttt{1001}\\},\\\\"
    )
    eq_lines.append(
        "|X^{\\mathrm{bdry}}_6|"
        " &= F_4 = 3,\\qquad X^{\\mathrm{bdry}}_6=\\{\\texttt{100001},\\ \\texttt{100101},\\ \\texttt{101001}\\},\\\\"
    )
    # Split X_8^{bdry} across two lines for readability.
    eq_lines.append(
        "|X^{\\mathrm{bdry}}_8|"
        " &= F_6 = 8,\\qquad X^{\\mathrm{bdry}}_8=\\{\\texttt{"
        + bdry8[0]
        + "},\\ \\texttt{"
        + bdry8[1]
        + "},\\ \\texttt{"
        + bdry8[2]
        + "},\\ \\texttt{"
        + bdry8[3]
        + "},\\\\"
    )
    eq_lines.append(
        " &\\qquad\\qquad\\qquad\\qquad\\qquad\\quad"
        " \\texttt{"
        + bdry8[4]
        + "},\\ \\texttt{"
        + bdry8[5]
        + "},\\ \\texttt{"
        + bdry8[6]
        + "},\\ \\texttt{"
        + bdry8[7]
        + "}\\},\\\\"
    )
    eq_lines.append(
        "|X^{\\mathrm{bdry}}_4|+|X^{\\mathrm{bdry}}_6|+|X^{\\mathrm{bdry}}_8|"
        " &= 1+3+8 = 12."
    )
    eq_lines.append("\\end{aligned}")
    eq_lines.append("\\]")
    eq_lines.append("")

    tex_eq.parent.mkdir(parents=True, exist_ok=True)
    tex_eq.write_text("\n".join(eq_lines), encoding="utf-8")

    # --- LaTeX table fragment (Zeckendorf--Fibonacci signatures) ---
    tab_lines: List[str] = []
    tab_lines.append("% AUTO-GENERATED by scripts/exp_boundary_tower_gut_signatures.py")
    tab_lines.append("\\begin{table}[H]")
    tab_lines.append("\\centering")
    tab_lines.append("\\small")
    tab_lines.append("\\setlength{\\tabcolsep}{7pt}")
    tab_lines.append("\\renewcommand{\\arraystretch}{1.12}")
    tab_lines.append(
        "\\caption{Zeckendorf--Fibonacci resolution signatures from boundary counts "
        "$|X_m^{\\mathrm{bdry}}|=F_{m-2}$. For a Lie algebra $\\mathfrak g$ with "
        "$D=\\dim\\mathfrak g$ (boson count), the Zeckendorf decomposition "
        "$D=\\sum_{k\\in S}F_k$ (no adjacent indices) yields the unique layer set "
        "$\\Sigma(\\mathfrak g)=\\{k+2:k\\in S\\}$ such that "
        "$D=\\sum_{m\\in\\Sigma(\\mathfrak g)}|X_m^{\\mathrm{bdry}}|$.}"
    )
    tab_lines.append("\\label{tab:zeckendorf_gut_signatures}")
    tab_lines.append("\\begin{tabular}{l r l l}")
    tab_lines.append("\\toprule")
    tab_lines.append("$\\mathfrak g$ & $D$ & Zeckendorf & $\\Sigma(\\mathfrak g)$ \\\\")
    tab_lines.append("\\midrule")
    for r in rows:
        name = str(r["name_tex"])
        D = int(r["D"])
        picks = [int(x) for x in r["zeckendorf_indices"]]  # descending
        sigma = [int(x) for x in r["sigma_layers"]]
        ztex = "$" + _tex_zeckendorf_sum(D, picks) + "$"
        stex = "$" + _tex_set_int(sigma) + "$"
        tab_lines.append(f"${name}$ & {D} & {ztex} & {stex} \\\\")
    tab_lines.append("\\bottomrule")
    tab_lines.append("\\end{tabular}")
    tab_lines.append("\\end{table}")
    tab_lines.append("")

    tex_tab.parent.mkdir(parents=True, exist_ok=True)
    tex_tab.write_text("\n".join(tab_lines), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate boundary-tower + Zeckendorf-GUT signature fragments.")
    parser.add_argument(
        "--tex-eq",
        type=str,
        default=str(generated_dir() / "eq_boundary_tower_sm12.tex"),
        help="Output LaTeX equation path.",
    )
    parser.add_argument(
        "--tex-tab",
        type=str,
        default=str(generated_dir() / "tab_zeckendorf_gut_signatures.tex"),
        help="Output LaTeX table path.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "boundary_tower_gut_signatures.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    write_outputs(tex_eq=Path(args.tex_eq), tex_tab=Path(args.tex_tab), json_out=Path(args.json_out))
    print(f"[boundary_tower_gut] wrote {args.tex_eq}", flush=True)
    print(f"[boundary_tower_gut] wrote {args.tex_tab}", flush=True)
    print(f"[boundary_tower_gut] wrote {args.json_out}", flush=True)


if __name__ == "__main__":
    main()

