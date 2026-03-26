#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Max-fiber achievers (phase structure) for Fold_m via modular DP.

Recall (proved in the paper) the congruence characterization:
  Fold_m(omega)=Fold_m(omega')  <->  N(omega) ≡ N(omega') (mod F_{m+2}),
and define residue counts:
  c_m(r) = #{ omega in {0,1}^m : N(omega) ≡ r (mod F_{m+2}) }.
Then for the unique stable type x with V_m(x)=r we have d_m(x)=c_m(r), hence
  D_m := max_x d_m(x) = max_r c_m(r),
and the number of maximizers equals #{r: c_m(r)=D_m}.

This script computes, for m<=M:
  - D_m (closed form, for consistency check),
  - D_m (DP),
  - kappa_m^{max} := #{ maximizers },
  - representative maximizer stable words (Zeckendorf/greedy map r -> x in X_m).

Outputs:
  - artifacts/export/fold_max_fiber_achievers_phase.json
  - sections/generated/tab_fold_max_fiber_achievers_phase.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List

import numpy as np

from common_mod_fib_dp import counts_mod_fib
from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


def fib_upto(n: int) -> List[int]:
    if n < 0:
        raise ValueError("n must be >= 0")
    F = [0, 1]
    for _ in range(2, n + 1):
        F.append(F[-1] + F[-2])
    return F[: n + 1]


def D_closed(m: int) -> int:
    if m < 2:
        raise ValueError("m must be >= 2")
    F = fib_upto((m // 2) + 2)
    if m % 2 == 0:
        k = m // 2
        return int(F[k + 2])
    # odd: D_{2k+1} = 2F_{k+1}
    k = (m - 1) // 2
    return int(2 * F[k + 1])


def D2_closed(m: int) -> int | None:
    """
    Closed form for the second-largest multiplicity D_m^{(2)}.

    Valid for m>=10 (equivalently k=floor(m/2)>=5), matching the paper's theorem:
      D_m^{(2)} = D_m - F_{floor(m/2)-4}.
    """
    if m < 10:
        return None
    k = m // 2
    F = fib_upto(k + 2)
    return int(D_closed(m) - F[k - 4])


def D3_closed(m: int) -> int | None:
    """
    Closed form for the third-largest multiplicity D_m^{(3)}.

    Even branch (proved in paper): for m=2k with k>=6 (m>=12),
      D_{2k}^{(3)} = F_{k+2} - F_{k-3}.

    Odd branch (DP-stabilized in the audited Table 8 / m<=32 window): for m=2k+1 with k>=9 (m>=19),
      D_{2k+1}^{(3)} = 2F_{k+1} - (F_{k-4}+F_{k-8}).

    Returns None outside the stable regime.
    """
    if m < 12:
        return None

    if m % 2 == 0:
        k = m // 2
        if k < 6:
            return None
        F = fib_upto(k + 2)
        return int(F[k + 2] - F[k - 3])

    k = (m - 1) // 2
    if k < 9:
        return None
    F = fib_upto(k + 1)
    return int(2 * F[k + 1] - (F[k - 4] + F[k - 8]))


def zeckendorf_word(m: int, r: int) -> str:
    """
    Return the unique x in X_m (no adjacent 11) with value V_m(x)=r,
    where V_m(x)=sum_{k=1}^m x_k F_{k+1} and 0<=r<F_{m+2}.
    """
    if m < 1:
        raise ValueError("m must be >= 1")
    F = fib_upto(m + 2)
    if r < 0 or r >= F[m + 2]:
        raise ValueError("r out of range for modulus F_{m+2}")

    rem = int(r)
    x = [0] * m
    prev_one = False  # track adjacency on descending greedy (higher index is next)
    for k in range(m, 0, -1):
        w = F[k + 1]
        if (not prev_one) and rem >= w:
            x[k - 1] = 1
            rem -= w
            prev_one = True
        else:
            x[k - 1] = 0
            prev_one = False
    if rem != 0:
        raise ValueError("Greedy Zeckendorf failed to exhaust remainder")
    # sanity: no adjacent 11
    for i in range(m - 1):
        if x[i] == 1 and x[i + 1] == 1:
            raise ValueError("Adjacent 11 produced (should not happen)")
    return "".join(str(b) for b in x)


@dataclass(frozen=True)
class Row:
    m: int
    D_closed: int
    D_dp: int
    D2_dp: int
    D3_dp: int
    gap_ratio: float
    gap3_ratio: float
    kappa: int
    residues: List[int]
    words: List[str]


def write_table_tex(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Max-fiber achiever multiplicity for Fold$_m$ via modular DP. "
        "$\\kappa_m^{\\mathrm{max}}$ counts the number of stable types $x\\in X_m$ attaining $d_m(x)=D_m$. "
        "Equivalently, $\\kappa_m^{\\mathrm{max}}=\\#\\{r\\in\\mathbb{Z}/F_{m+2}\\mathbb{Z}: c_m(r)=D_m\\}$ for residue counts $c_m$. "
        "We also report the next two distinct spectrum levels $D_m^{(2)}$ and $D_m^{(3)}$. "
        "Representative maximizers are shown only for the largest $m$ in the window.}"
    )
    lines.append("\\label{tab:fold_max_fiber_achievers_phase}")
    lines.append("\\begin{tabular}{r r r r r r l}")
    lines.append("\\toprule")
    lines.append(
        "$m$ & $D_m$ (closed) & $D_m$ (DP) & $D_m^{(2)}$ (DP) & $D_m^{(2)}/D_m$ & $D_m^{(3)}$ (DP) & representative maximizers\\\\"
    )
    lines.append("\\midrule")
    m_max = max(r.m for r in rows) if rows else 0
    show_ms = {m_max, m_max - 1} if m_max >= 3 else {m_max}
    for r in rows:
        if r.m in show_ms:
            ex = ",\\;".join([f"\\texttt{{{w}}}" for w in r.words])
        else:
            ex = "--"
        lines.append(
            f"{r.m} & {r.D_closed} & {r.D_dp} & {r.D2_dp} & {r.gap_ratio:.6f} & {r.D3_dp} & {ex}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Max-fiber achievers and phase representatives (m<=M).")
    parser.add_argument("--m-min", type=int, default=2)
    parser.add_argument("--m-max", type=int, default=30)
    parser.add_argument("--show-words", type=int, default=4, help="How many maximizer words to record per m.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_max_fiber_achievers_phase.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_max_fiber_achievers_phase.tex"),
    )
    args = parser.parse_args()

    if args.m_min < 2 or args.m_max < args.m_min:
        raise SystemExit("Require m_max >= m_min >= 2")
    if args.show_words < 1:
        raise SystemExit("Require --show-words >= 1")

    prog = Progress("fold-max-fiber-achievers", every_seconds=20.0)

    rows: List[Row] = []
    for m in range(args.m_min, args.m_max + 1):
        c = counts_mod_fib(m, prog=prog)
        Ddp = int(np.max(c))
        # Second/third maxima (distinct values).
        vals = np.unique(c)
        vals_sorted = np.sort(vals)
        D2 = int(vals_sorted[-2]) if len(vals_sorted) >= 2 else int(Ddp)
        D3 = int(vals_sorted[-3]) if len(vals_sorted) >= 3 else int(D2)
        gap_ratio = float(D2 / Ddp) if Ddp > 0 else float("nan")
        gap3_ratio = float(D3 / Ddp) if Ddp > 0 else float("nan")
        residues = np.flatnonzero(c == Ddp).astype(int).tolist()
        kappa = int(len(residues))

        Dc = D_closed(m)
        if Ddp != Dc:
            raise ValueError(f"D mismatch at m={m}: DP={Ddp}, closed={Dc}")

        D2c = D2_closed(m)
        if D2c is not None and D2 != D2c:
            raise ValueError(f"D2 mismatch at m={m}: DP={D2}, closed={D2c}")

        D3c = D3_closed(m)
        if D3c is not None and D3 != D3c:
            raise ValueError(f"D3 mismatch at m={m}: DP={D3}, closed={D3c}")

        # Representative words (by smallest residues)
        residues_sorted = sorted(residues)[: args.show_words]
        words = [zeckendorf_word(m, r) for r in residues_sorted]

        rows.append(
            Row(
                m=m,
                D_closed=Dc,
                D_dp=Ddp,
                D2_dp=D2,
                D3_dp=D3,
                gap_ratio=gap_ratio,
                gap3_ratio=gap3_ratio,
                kappa=kappa,
                residues=residues_sorted,
                words=words,
            )
        )
        print(
            f"[fold-max-fiber] m={m} mod={len(c)} D={Ddp} D2={D2} D3={D3} gap2={gap_ratio:.6f} gap3={gap3_ratio:.6f} kappa={kappa}",
            flush=True,
        )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    payload = {"m_min": int(args.m_min), "m_max": int(args.m_max), "rows": [asdict(r) for r in rows]}
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[fold-max-fiber] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[fold-max-fiber] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

