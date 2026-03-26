#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: affine geometry classification of Fold^{bin}_6 fibers in F_2^6.

All output is English-only by repository convention.

We identify Omega_6 = {0,1}^6 with the affine space F_2^6 via the standard
binary encoding n in {0,...,63}. Addition is bitwise XOR.

For each stable type w in X_6, define the dyadic fiber
  F_w := (Fold^{bin}_6)^{-1}(w) subset F_2^6.

We compute:
  - fiber size d^{bin}_6(w),
  - affine span dimension affdim(F_w),
  - whether F_w is an affine subspace (coset of a linear subspace).

In particular, at m=6 we certify:
  - 8 fibers are affine 1-flats (size 2),
  - 3 fibers are affine 2-flats (size 4),
  - the remaining 10 fibers are not affine subspaces (4 of size 3, 6 of size 4).

Outputs:
  - artifacts/export/foldbin6_fiber_affine_geometry.json
  - sections/generated/tab_foldbin6_fiber_affine_geometry.tex
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import fib_upto, word_to_str, zeckendorf_digits


def _K_of_limit(limit: int) -> int:
    """Unique K with F_{K+1} <= limit < F_{K+2} (F_1=F_2=1)."""
    if limit < 0:
        raise ValueError("limit must be non-negative")
    fib = [1, 1]
    while fib[-1] <= limit:
        fib.append(fib[-1] + fib[-2])
    return len(fib) - 2


def _fold_bin_prefix_word(N: int, m: int) -> str:
    """Compute Fold^{bin}_m(N) = prefix_m(Zeckendorf(N)) as an m-bit string."""
    limit = (1 << m) - 1
    if not (0 <= N <= limit):
        raise ValueError(f"N must be in [0,{limit}] for m={m}")
    K = _K_of_limit(limit)
    digits = zeckendorf_digits(N, K)  # c_1..c_K
    return word_to_str(digits[:m])


def _rank_f2(vs: List[int], nbits: int) -> int:
    """Rank over F_2 of vectors encoded as integers in nbits."""
    basis = [0] * nbits
    r = 0
    for v in vs:
        x = v
        for i in range(nbits - 1, -1, -1):
            if (x >> i) & 1:
                if basis[i]:
                    x ^= basis[i]
                else:
                    basis[i] = x
                    r += 1
                    break
    return r


def _affine_dim(points: List[int], nbits: int) -> int:
    if len(points) <= 1:
        return 0
    p0 = points[0]
    diffs = [p ^ p0 for p in points[1:]]
    return _rank_f2(diffs, nbits)


def _is_affine_subspace(points: List[int]) -> bool:
    """Affine subspace iff size is power of 2 and difference set is linear subspace."""
    n = len(points)
    if n == 0:
        return False
    if n & (n - 1):
        return False
    p0 = points[0]
    L = {p ^ p0 for p in points}
    for a in L:
        for b in L:
            if (a ^ b) not in L:
                return False
    return True


def _int_to_bits_str(n: int, m: int) -> str:
    return format(n, f"0{m}b")


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit affine geometry of Fold^{bin}_6 fibers in F_2^6.")
    ap.add_argument("--m", type=int, default=6)
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "foldbin6_fiber_affine_geometry.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_foldbin6_fiber_affine_geometry.tex"),
    )
    args = ap.parse_args()

    m = int(args.m)
    if m != 6:
        raise ValueError("This audit is anchored at m=6 (use --m 6).")

    limit = (1 << m) - 1
    fibers: Dict[str, List[int]] = defaultdict(list)
    for N in range(0, limit + 1):
        w = _fold_bin_prefix_word(N, m)
        fibers[w].append(N)

    rows: List[Dict[str, object]] = []
    counts = Counter()

    affine_planes: List[str] = []
    affine_lines: List[str] = []
    nonaffine_size4: List[str] = []
    size3_words: List[str] = []

    for w in sorted(fibers.keys()):
        pts = sorted(fibers[w])
        d = len(pts)
        affdim = _affine_dim(pts, m)
        is_aff = _is_affine_subspace(pts)

        if is_aff and d == 2:
            cls = "affine_1_flat"
            affine_lines.append(w)
        elif is_aff and d == 4:
            cls = "affine_2_flat"
            affine_planes.append(w)
        elif d == 3:
            cls = "non_affine_plane_minus_one_point"
            size3_words.append(w)
        elif d == 4:
            cls = "non_affine_subset_of_affine_3_flat"
            nonaffine_size4.append(w)
        else:
            cls = "other"

        counts[cls] += 1

        missing_point_bits = None
        if d == 3:
            miss = pts[0] ^ pts[1] ^ pts[2]
            missing_point_bits = _int_to_bits_str(miss, m)

        rows.append(
            {
                "w": w,
                "fiber_size": d,
                "affine_dim": affdim,
                "is_affine_subspace": is_aff,
                "class": cls,
                "points_int": pts,
                "points_bits": [_int_to_bits_str(p, m) for p in pts],
                "missing_plane_point_bits_if_size3": missing_point_bits,
            }
        )

    payload = {
        "m": m,
        "domain_size": 1 << m,
        "X_size": len(fibers),
        "class_counts": {k: int(v) for k, v in sorted(counts.items())},
        "affine_lines_words": affine_lines,
        "affine_planes_words": affine_planes,
        "nonaffine_size4_words": nonaffine_size4,
        "size3_words": size3_words,
        "rows": rows,
    }

    json_out = Path(str(args.json_out))
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # TeX table.
    tex_out = Path(str(args.tex_out))
    tex_out.parent.mkdir(parents=True, exist_ok=True)

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_foldbin6_fiber_affine_geometry.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.10}")
    lines.append(
        "\\caption{Affine geometry classification of dyadic fibers $F_w=(\\mathrm{Fold}^{\\mathrm{bin}}_6)^{-1}(w)\\subset \\mathbb{F}_2^6$ "
        "(points encoded by the standard $6$-bit binary word). We report the fiber size, the affine-span dimension, and whether the fiber is an affine subspace.}"
    )
    lines.append("\\label{tab:foldbin6_fiber_affine_geometry}")
    lines.append("\\begin{tabular}{r l r r c l}")
    lines.append("\\toprule")
    lines.append("index & $w\\in X_6$ & $|F_w|$ & $\\dim_{\\mathrm{aff}}(F_w)$ & affine? & class\\\\")
    lines.append("\\midrule")
    for i, r in enumerate(rows, start=1):
        w = str(r["w"])
        d = int(r["fiber_size"])
        ad = int(r["affine_dim"])
        ia = bool(r["is_affine_subspace"])
        cls = str(r["class"]).replace("_", "\\_")
        yesno = "Y" if ia else "N"
        lines.append(f"{i} & \\texttt{{{w}}} & {d} & {ad} & {yesno} & {cls}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")
    tex_out.write_text("\n".join(lines), encoding="utf-8")

    print(f"File: {json_out.relative_to(json_out.parents[2])}")
    print(f"File: {tex_out.relative_to(tex_out.parents[2])}")


if __name__ == "__main__":
    main()

