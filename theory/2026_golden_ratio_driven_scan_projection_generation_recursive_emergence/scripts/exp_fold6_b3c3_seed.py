#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Fold6 (m=6) B3/C3 Lie-seed audit artifacts from the rigid 18 ⊕ 3 split.

All output is English-only by repository convention (tables/equations are LaTeX).

At m=6, the golden-mean legal language X_6 has size 21 and splits as
  X_6 = X_6^{cyc} ⊔ X_6^{bdry},   |X_6^{cyc}|=18, |X_6^{bdry}|=3,
where bdry are endpoint words with u_1=u_6=1.

Inside the cyclic sector there is an additional clean "two-length fingerprint":
  #{w in X_6^{cyc} : wt(w)=1} = 6,
  #{w in X_6^{cyc} : wt(w)≠1} = 12.

Reading the 3 boundary types as Cartan-like commuting directions and the 18 cyclic
types as root-like charged directions, the count 3+18=21 matches a rank-3 simple
Lie algebra with 18 roots (dim 21), forcing type B3/C3 (long/short swapped duals).

This script exports:
  - artifacts/export/fold6_b3c3_seed.json
  - sections/generated/eq_fold6_b3c3_seed.tex
  - sections/generated/tab_fold6_b3c3_root_dictionary_B3.tex
  - sections/generated/tab_fold6_b3c3_root_dictionary_C3.tex
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import fib_upto, word_to_str

RootVec = Tuple[int, int, int]


def _golden_words(m: int) -> List[List[int]]:
    """All length-m binary words with no adjacent ones (golden mean SFT)."""
    if m < 0:
        raise ValueError("m must be non-negative")
    out: List[List[int]] = []

    def rec(pos: int, prev1: int, acc: List[int]) -> None:
        if pos == m:
            out.append(list(acc))
            return
        acc.append(0)
        rec(pos + 1, 0, acc)
        acc.pop()
        if prev1 == 0:
            acc.append(1)
            rec(pos + 1, 1, acc)
            acc.pop()

    rec(0, 0, [])
    return out


def _is_boundary_word(w: str) -> bool:
    return len(w) == 6 and w[0] == "1" and w[-1] == "1"


def _hamming_weight(w: str) -> int:
    return w.count("1")


def _V_m(w: str) -> int:
    """Zeckendorf value V_m(w)=sum_{k=1}^m w_k F_{k+1}, with F_1=F_2=1."""
    m = len(w)
    if m <= 0:
        return 0
    fib = fib_upto(m + 2)  # F_1..F_{m+2}
    # position k has weight F_{k+1}; in 0-based indexing this is fib[i+1]
    return sum((1 if ch == "1" else 0) * int(fib[i + 1]) for i, ch in enumerate(w))


def _roots_B3() -> Tuple[List[RootVec], List[RootVec]]:
    """
    Return (short_roots, long_roots) for B3 in the standard e_i basis:
      short: ±e_i  (6)
      long:  ±e_i ± e_j (12)
    """
    short: List[RootVec] = [
        (+1, 0, 0),
        (-1, 0, 0),
        (0, +1, 0),
        (0, -1, 0),
        (0, 0, +1),
        (0, 0, -1),
    ]
    long: List[RootVec] = [
        (+1, +1, 0),
        (+1, -1, 0),
        (-1, +1, 0),
        (-1, -1, 0),
        (+1, 0, +1),
        (+1, 0, -1),
        (-1, 0, +1),
        (-1, 0, -1),
        (0, +1, +1),
        (0, +1, -1),
        (0, -1, +1),
        (0, -1, -1),
    ]
    return short, long


def _roots_C3() -> Tuple[List[RootVec], List[RootVec]]:
    """
    Return (short_roots, long_roots) for C3 in the standard e_i basis:
      short: ±e_i ± e_j (12)
      long:  ±2 e_i (6)
    """
    short12 = _roots_B3()[1]  # same as B3 long roots in this coordinate model
    long6: List[RootVec] = [
        (+2, 0, 0),
        (-2, 0, 0),
        (0, +2, 0),
        (0, -2, 0),
        (0, 0, +2),
        (0, 0, -2),
    ]
    return short12, long6


def _word_axis_for_weight1(w: str) -> int:
    """
    Assign one of three Cartan axes to a weight=1 word, by its 1-position.

    We group the 6 singleton directions into three involutive pairs:
      axis 1 : positions 1 and 6  -> {100000, 000001}
      axis 2 : positions 2 and 5  -> {010000, 000010}
      axis 3 : positions 3 and 4  -> {001000, 000100}
    """
    if len(w) != 6 or _hamming_weight(w) != 1:
        raise ValueError("expected a 6-bit word of Hamming weight 1")
    pos = w.index("1")  # 0-based
    if pos in (0, 5):
        return 1
    if pos in (1, 4):
        return 2
    if pos in (2, 3):
        return 3
    raise AssertionError("unreachable")


def _sign_for_weight1(w: str) -> int:
    """Deterministic sign (+1 or -1) within each axis pair: left position is +, right is -."""
    if len(w) != 6 or _hamming_weight(w) != 1:
        raise ValueError("expected a 6-bit word of Hamming weight 1")
    pos = w.index("1")  # 0-based
    return +1 if pos in (0, 1, 2) else -1


def _build_dictionary(*, cyc_words: Sequence[str], variant: str) -> Dict[str, RootVec]:
    """
    Build a deterministic bijection:
      X6^{cyc}  ->  Φ(B3) or Φ(C3),
    returning word -> rootvec.
    """
    if variant not in ("B3", "C3"):
        raise ValueError("variant must be 'B3' or 'C3'")
    if len(cyc_words) != 18:
        raise ValueError("expected |X6^{cyc}|=18")

    cyc = list(cyc_words)
    cyc_w1 = [w for w in cyc if _hamming_weight(w) == 1]
    cyc_rest = [w for w in cyc if _hamming_weight(w) != 1]
    if len(cyc_w1) != 6 or len(cyc_rest) != 12:
        raise AssertionError("Expected cyclic weight split 6+12.")

    if variant == "B3":
        short6, long12 = _roots_B3()
        weight1_roots = short6
        rest_roots = long12
    else:
        short12, long6 = _roots_C3()
        weight1_roots = long6
        rest_roots = short12

    # Map the 6 weight=1 words to the 6 axial roots (one nonzero coordinate).
    axis_to_pm: Dict[int, Tuple[RootVec, RootVec]] = {}
    for rv in weight1_roots:
        nz = [i for i, x in enumerate(rv) if x != 0]
        if len(nz) != 1:
            raise AssertionError(f"Unexpected axial root shape: {rv}")
        a = int(nz[0] + 1)  # 1..3
        if rv[nz[0]] > 0:
            axis_to_pm[a] = (rv, (-rv[0], -rv[1], -rv[2]))
    if set(axis_to_pm.keys()) != {1, 2, 3}:
        raise AssertionError("Failed to build axis +/- roots for all three axes.")

    out: Dict[str, RootVec] = {}
    for w in cyc_w1:
        ax = _word_axis_for_weight1(w)
        sgn = _sign_for_weight1(w)
        pos, neg = axis_to_pm[ax]
        out[w] = pos if sgn > 0 else neg

    # Map remaining 12 cyclic words to the remaining 12 roots deterministically.
    cyc_rest_sorted = sorted(cyc_rest, key=lambda w: (_V_m(w), w))
    rest_roots_sorted = list(rest_roots)  # deterministic constructor order
    for w, rv in zip(cyc_rest_sorted, rest_roots_sorted, strict=True):
        out[w] = rv

    if len(out) != 18 or len(set(out.values())) != 18:
        raise AssertionError("Dictionary is not a bijection on cyclic types.")
    return out


def _signed_permutations_WB3() -> List[Tuple[Tuple[int, int, int], Tuple[int, int, int]]]:
    """W(B3)=W(C3) as signed permutations of three coordinates (order 48)."""
    perms = [
        (0, 1, 2),
        (0, 2, 1),
        (1, 0, 2),
        (1, 2, 0),
        (2, 0, 1),
        (2, 1, 0),
    ]
    signs = [(a, b, c) for a in (-1, 1) for b in (-1, 1) for c in (-1, 1)]
    return [(p, s) for p in perms for s in signs]


def _act_signed_perm(v: RootVec, p: Tuple[int, int, int], s: Tuple[int, int, int]) -> RootVec:
    vv = (v[p[0]], v[p[1]], v[p[2]])
    return (s[0] * vv[0], s[1] * vv[1], s[2] * vv[2])


def _orbit_size_hist(words: Sequence[str], mapping: Dict[str, RootVec]) -> Dict[int, int]:
    inv = {rv: w for (w, rv) in mapping.items()}
    W = _signed_permutations_WB3()
    hist: Dict[int, int] = {}
    for w0 in words:
        rv0 = mapping[w0]
        orb: set[str] = set()
        for (p, s) in W:
            rv = _act_signed_perm(rv0, p=p, s=s)
            if rv in inv:
                orb.add(inv[rv])
        hist[len(orb)] = hist.get(len(orb), 0) + 1
    return dict(sorted(hist.items()))


@dataclass(frozen=True)
class Report:
    X6_size: int
    cyc_size: int
    bdry_size: int
    bdry_words: List[str]
    cyc_weight_hist: Dict[int, int]
    cyc_weight1_words: List[str]
    cyc_nonweight1_words: List[str]
    b3_dict: Dict[str, RootVec]
    c3_dict: Dict[str, RootVec]
    weyl_group_order: int
    weyl_orbit_hist_B3: Dict[int, int]
    weyl_orbit_hist_C3: Dict[int, int]


def _write_tex_eq(report: Report, out_path: Path) -> None:
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_fold6_b3c3_seed.py")
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append(
        rf"|X_6|&={report.X6_size},\qquad |X_6^{{\mathrm{{cyc}}}}|={report.cyc_size},\qquad |X_6^{{\mathrm{{bdry}}}}|={report.bdry_size},\\"
    )
    bd = ",\\ ".join([f"\\texttt{{{w}}}" for w in report.bdry_words])
    lines.append(rf"X_6^{{\mathrm{{bdry}}}}&=\{{{bd}\}},\\")
    hist_tex = ",\\ ".join([f"{k}:{v}" for k, v in sorted(report.cyc_weight_hist.items())])
    lines.append(rf"\mathrm{{wt}}\text{{-hist}}(X_6^{{\mathrm{{cyc}}}})&=\{{{hist_tex}\}},\\")
    lines.append(
        rf"\#\{{w\in X_6^{{\mathrm{{cyc}}}}:\ \mathrm{{wt}}(w)=1\}}&={len(report.cyc_weight1_words)},\qquad \#\{{w\in X_6^{{\mathrm{{cyc}}}}:\ \mathrm{{wt}}(w)\neq 1\}}={len(report.cyc_nonweight1_words)}."
    )
    lines.append("\\end{aligned}")
    lines.append("\\]")
    lines.append("")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines), encoding="utf-8")


def _write_tex_table(
    mapping: Dict[str, RootVec],
    *,
    caption: str,
    label: str,
    out_path: Path,
    alias_labels: List[str] | None = None,
) -> None:
    rows = sorted(mapping.items(), key=lambda kv: (_V_m(kv[0]), kv[0]))
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_fold6_b3c3_seed.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\small")
    lines.append("\\setlength{\\tabcolsep}{10pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.10}")
    lines.append(f"\\caption{{{caption}}}")
    lines.append(f"\\label{{{label}}}")
    for alias in alias_labels or []:
        lines.append(f"\\label{{{alias}}}")
    lines.append("\\begin{tabular}{l r r}")
    lines.append("\\toprule")
    lines.append("$w\\in X_6^{\\mathrm{cyc}}$ & $\\mathrm{wt}(w)$ & root vector\\\\")
    lines.append("\\midrule")
    for w, rv in rows:
        wt = _hamming_weight(w)
        lines.append(f"\\texttt{{{w}}} & {wt} & $({rv[0]},{rv[1]},{rv[2]})$\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Fold6 B3/C3 root-seed audit artifacts.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold6_b3c3_seed.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-eq",
        type=str,
        default=str(generated_dir() / "eq_fold6_b3c3_seed.tex"),
        help="Output LaTeX equation fragment path.",
    )
    parser.add_argument(
        "--tex-b3",
        type=str,
        default=str(generated_dir() / "tab_fold6_b3c3_root_dictionary_B3.tex"),
        help="Output LaTeX table fragment path (B3 dictionary).",
    )
    parser.add_argument(
        "--tex-c3",
        type=str,
        default=str(generated_dir() / "tab_fold6_b3c3_root_dictionary_C3.tex"),
        help="Output LaTeX table fragment path (C3 dictionary).",
    )
    args = parser.parse_args()

    X6 = [word_to_str(w) for w in _golden_words(6)]
    bdry = sorted([w for w in X6 if _is_boundary_word(w)])
    cyc = sorted([w for w in X6 if not _is_boundary_word(w)])
    if len(X6) != 21 or len(cyc) != 18 or len(bdry) != 3:
        raise AssertionError("Unexpected X6 / cyclic / boundary sizes.")

    cyc_weight_hist = Counter(_hamming_weight(w) for w in cyc)
    cyc_w1 = sorted([w for w in cyc if _hamming_weight(w) == 1])
    cyc_rest = sorted([w for w in cyc if _hamming_weight(w) != 1])
    if len(cyc_w1) != 6 or len(cyc_rest) != 12:
        raise AssertionError("Expected cyclic weight split 6+12.")

    b3_dict = _build_dictionary(cyc_words=cyc, variant="B3")
    c3_dict = _build_dictionary(cyc_words=cyc, variant="C3")

    W = _signed_permutations_WB3()
    if len(W) != 48:
        raise AssertionError("Expected |W(B3)|=48.")

    report = Report(
        X6_size=len(X6),
        cyc_size=len(cyc),
        bdry_size=len(bdry),
        bdry_words=list(bdry),
        cyc_weight_hist=dict(sorted(cyc_weight_hist.items())),
        cyc_weight1_words=list(cyc_w1),
        cyc_nonweight1_words=list(cyc_rest),
        b3_dict=b3_dict,
        c3_dict=c3_dict,
        weyl_group_order=len(W),
        weyl_orbit_hist_B3=_orbit_size_hist(cyc, b3_dict),
        weyl_orbit_hist_C3=_orbit_size_hist(cyc, c3_dict),
    )

    # JSON (export)
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(
        json.dumps(
            {
                "X6_size": report.X6_size,
                "cyc_size": report.cyc_size,
                "bdry_size": report.bdry_size,
                "bdry_words": report.bdry_words,
                "cyc_weight_hist": report.cyc_weight_hist,
                "cyc_weight1_words": report.cyc_weight1_words,
                "cyc_nonweight1_words": report.cyc_nonweight1_words,
                "B3_dictionary": report.b3_dict,
                "C3_dictionary": report.c3_dict,
                "weyl_group_order": report.weyl_group_order,
                "weyl_orbit_size_hist_B3": report.weyl_orbit_hist_B3,
                "weyl_orbit_size_hist_C3": report.weyl_orbit_hist_C3,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    # LaTeX fragments
    _write_tex_eq(report, Path(args.tex_eq))
    _write_tex_table(
        report.b3_dict,
        caption="A deterministic identification (dictionary) of $X_6^{\\mathrm{cyc}}$ with the $B_3$ root system (choice of normalization).",
        label="tab:fold6_b3c3_root_dictionary_B3",
        out_path=Path(args.tex_b3),
        alias_labels=["tab:fold6_b3c3_root_dictionary_b3"],
    )
    _write_tex_table(
        report.c3_dict,
        caption="A deterministic identification (dictionary) of $X_6^{\\mathrm{cyc}}$ with the $C_3$ root system (long/short swapped normalization).",
        label="tab:fold6_b3c3_root_dictionary_c3",
        out_path=Path(args.tex_c3),
    )

    print(f"[fold6-b3c3-seed] wrote {jout}", flush=True)
    print(f"[fold6-b3c3-seed] wrote {args.tex_eq}", flush=True)
    print(f"[fold6-b3c3-seed] wrote {args.tex_b3}", flush=True)
    print(f"[fold6-b3c3-seed] wrote {args.tex_c3}", flush=True)
    print("[fold6-b3c3-seed] done", flush=True)


if __name__ == "__main__":
    main()

