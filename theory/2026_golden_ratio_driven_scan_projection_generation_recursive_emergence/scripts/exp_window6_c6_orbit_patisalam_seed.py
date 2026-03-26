#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Window-6 (m=6) C6 rotation-orbit decomposition and Pati–Salam Levi-skeleton audit.

All code is English-only by repository convention.

At m=6, the golden-mean legal language X_6 has size 21 and splits as:
  X_6 = X_6^{cyc} ⊔ X_6^{bdry},   |X_6^{cyc}|=18, |X_6^{bdry}|=3,
where the boundary sector is the endpoint-(1,1) fiber (u_1=u_6=1).

On the cyclic sector, the cyclic-rotation action of C6 preserves admissibility and
induces a rigid orbit multiset with sizes {1,2,3,6,6}. This yields a canonical
15 ⊕ 3 refinement inside X_6^{cyc}, hence a 21=15⊕3⊕3 Levi-type dimension skeleton
(candidate match for su(4) ⊕ su(2) ⊕ su(2)).

We also extract the dyadic (binary-interval) fold at m=6:
  Fold^{bin}_6 : {0,...,63} -> X_6,
and certify the boundary-sector two-sheet lift: each boundary word has exactly two
preimages differing by 34 (=F_9), giving a canonical Z2 "sheet parity".

Outputs:
  - artifacts/export/window6_c6_orbit_patisalam_seed.json
  - sections/generated/eq_window6_c6_orbit_decomposition.tex
  - sections/generated/eq_window6_c6_character_decomposition.tex
  - sections/generated/tab_window6_c6_orbit_decomposition.tex
  - sections/generated/tab_window6_patisalam_9633_partition.tex
  - sections/generated/eq_fold6_bin_uplift_delta_set.tex
  - sections/generated/tab_fold6_bin_uplift_choice_collapse.tex
  - sections/generated/tab_fold6_boundary_sheet_pairs.tex
  - sections/generated/tab_foldbin_boundary_lift_m6_m8.tex
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Set, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import fib_upto, word_to_str, zeckendorf_digits


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


def _rot_left(w: str, k: int = 1) -> str:
    n = len(w)
    kk = k % n
    return w[kk:] + w[:kk]


def _hamming_weight(w: str) -> int:
    return w.count("1")


def _V_m(w: str) -> int:
    """Zeckendorf value V_m(w)=sum_{k=1}^m w_k F_{k+1}, with F_1=F_2=1."""
    m = len(w)
    if m <= 0:
        return 0
    fib = fib_upto(m + 2)  # F_1..F_{m+2}
    return sum((1 if ch == "1" else 0) * int(fib[i + 1]) for i, ch in enumerate(w))


def _K_of_m(m: int) -> int:
    """Return K(m) s.t. F_{K+1} <= 2^m-1 < F_{K+2} (F_1=F_2=1)."""
    if m < 0:
        raise ValueError("m must be non-negative")
    target = (1 << m) - 1
    # Fibonacci sequence by index (1-based): F_1=F_2=1.
    f1, f2 = 1, 1
    idx = 2
    while f2 <= target:
        f1, f2 = f2, f1 + f2
        idx += 1
    # Now F_idx = f2 > target and F_{idx-1} <= target.
    # We need K such that K+2 = idx.
    return idx - 2


def _fold_bin_prefix(n: int, *, m: int, K: int) -> str:
    """Fold^{bin}_m(n): Zeckendorf digits prefix of length m (compute digits up to K)."""
    if n < 0:
        raise ValueError("n must be non-negative")
    digits = zeckendorf_digits(n, K)  # digits for weights F_{k+1}, k=1..K
    return word_to_str(digits[:m])


def _tex_tt_set(words: Sequence[str]) -> str:
    # Example: \{\texttt{000001}, \texttt{000010}\}
    inner = ",\\ ".join([f"\\texttt{{{w}}}" for w in words])
    return "\\{" + inner + "\\}"


@dataclass(frozen=True)
class Orbit:
    rep: str
    size: int
    weight: int
    words: List[str]


def _compute_c6_orbits(words: Sequence[str]) -> List[Orbit]:
    """C6-orbits under left rotation (k=1), deterministic ordering."""
    universe: Set[str] = set(words)
    unseen: Set[str] = set(words)
    out: List[Orbit] = []
    while unseen:
        w0 = min(unseen)
        orb = {_rot_left(w0, k) for k in range(6)}
        if not orb.issubset(universe):
            bad = sorted(list(orb - universe))
            raise AssertionError(f"Rotation left orbit escaped universe: {bad}")
        unseen -= orb
        rep = min(orb)
        ws = sorted(list(orb))
        wt = _hamming_weight(rep)
        if any(_hamming_weight(w) != wt for w in ws):
            raise AssertionError("Hamming weight not invariant under rotation (unexpected).")
        out.append(Orbit(rep=rep, size=len(ws), weight=wt, words=ws))
    out.sort(key=lambda o: (o.size, o.rep))
    return out


def write_outputs(
    *,
    json_out: Path,
    tex_eq_orbit: Path,
    tex_eq_char: Path,
    tex_tab_orbit: Path,
    tex_tab_partition: Path,
    tex_eq_delta: Path,
    tex_tab_choice_collapse: Path,
    tex_tab_bdry: Path,
    tex_tab_bdry_stability: Path,
) -> None:
    # --- X6 split (cyclic/boundary) ---
    X6 = sorted([word_to_str(w) for w in _golden_words(6)])
    bdry = sorted([w for w in X6 if _is_boundary_word(w)])
    cyc = sorted([w for w in X6 if w not in set(bdry)])
    if len(X6) != 21 or len(cyc) != 18 or len(bdry) != 3:
        raise AssertionError("Unexpected X6 / cyclic / boundary sizes.")
    if bdry != ["100001", "100101", "101001"]:
        raise AssertionError(f"Unexpected boundary words at m=6: {bdry}")

    # --- C6 orbit decomposition on cyclic sector ---
    orbits = _compute_c6_orbits(cyc)
    orbit_sizes = sorted([o.size for o in orbits])
    if orbit_sizes != [1, 2, 3, 6, 6]:
        raise AssertionError(f"Unexpected orbit size multiset: {orbit_sizes}")

    # --- C6 character multiplicities for the permutation module C[X6_cyc] ---
    # For C6 with generator rho, the linear characters are chi_k(rho)=exp(2*pi*i*k/6), k=0..5.
    # A transitive orbit of size s corresponds to Ind_{C_{6/s}}^{C6} 1, hence contributes 1 to those
    # chi_k that are trivial on the stabilizer C_{6/s}, i.e. k ≡ 0 (mod 6/s).
    def _c6_mult_for_orbit_size(s: int) -> List[int]:
        if s <= 0 or 6 % s != 0:
            raise AssertionError(f"Bad orbit size for C6 action: {s}")
        stab = 6 // s
        return [1 if (k % stab == 0) else 0 for k in range(6)]

    m_total = [0] * 6
    for o in orbits:
        m_total = [a + b for a, b in zip(m_total, _c6_mult_for_orbit_size(o.size))]
    if m_total != [5, 2, 3, 3, 3, 2]:
        raise AssertionError(f"Unexpected C6 character multiplicities: {m_total}")

    big_orbits = [o for o in orbits if o.size in (3, 6)]
    small_orbits = [o for o in orbits if o.size in (1, 2)]
    big_sizes = sorted([o.size for o in big_orbits])
    small_sizes = sorted([o.size for o in small_orbits])
    if big_sizes != [3, 6, 6] or small_sizes != [1, 2]:
        raise AssertionError(f"Unexpected 15+3 orbit grouping: big={big_sizes} small={small_sizes}")

    m_big = [0] * 6
    for o in big_orbits:
        m_big = [a + b for a, b in zip(m_big, _c6_mult_for_orbit_size(o.size))]
    m_small = [0] * 6
    for o in small_orbits:
        m_small = [a + b for a, b in zip(m_small, _c6_mult_for_orbit_size(o.size))]
    if m_big != [3, 2, 3, 2, 3, 2] or m_small != [2, 0, 0, 1, 0, 0]:
        raise AssertionError(f"Unexpected big/small C6 multiplicities: big={m_big} small={m_small}")

    # Counts of induced-permutation building blocks, determined by orbit sizes.
    n_reg = sum(1 for o in orbits if o.size == 6)
    n_ind_c2 = sum(1 for o in orbits if o.size == 3)  # stabilizer order 2
    n_ind_c3 = sum(1 for o in orbits if o.size == 2)  # stabilizer order 3
    n_triv = sum(1 for o in orbits if o.size == 1)
    if (n_reg, n_ind_c2, n_ind_c3, n_triv) != (2, 1, 1, 1):
        raise AssertionError(
            "Unexpected induced-module term counts: "
            f"(Reg,Ind_C2,Ind_C3,triv)=({n_reg},{n_ind_c2},{n_ind_c3},{n_triv})"
        )

    # --- Rigid 9+6+3+3 four-block partition (weight-layered + boundary) ---
    cyc_wt1 = sorted([w for w in cyc if _hamming_weight(w) == 1])
    cyc_wt2 = sorted([w for w in cyc if _hamming_weight(w) == 2])
    cyc_wt0_or_3 = sorted([w for w in cyc if _hamming_weight(w) in (0, 3)])
    if (len(cyc_wt2), len(cyc_wt1), len(cyc_wt0_or_3), len(bdry)) != (9, 6, 3, 3):
        raise AssertionError(
            "Unexpected 9+6+3+3 partition sizes: "
            f"(wt2,wt1,wt0or3,bdry)=({len(cyc_wt2)},{len(cyc_wt1)},{len(cyc_wt0_or_3)},{len(bdry)})"
        )

    # --- Fold^{bin}_6 preimages and uplift deltas ---
    m = 6
    K = _K_of_m(m)
    if K != 9:
        raise AssertionError(f"Expected K(6)=9, got {K}")
    pre: Dict[str, List[int]] = {w: [] for w in X6}
    for n in range(0, 1 << m):
        w = _fold_bin_prefix(n, m=m, K=K)
        pre[w].append(n)
    if any(len(v) == 0 for v in pre.values()):
        missing = [w for w, v in pre.items() if len(v) == 0]
        raise AssertionError(f"Some X6 words have empty Fold^bin_6 preimage: {missing}")

    delta_global: Set[int] = set()
    delta_w6_1: Set[int] = set()
    for w, ns in pre.items():
        V = _V_m(w)
        ds = {int(n - V) for n in ns}
        delta_global |= ds
        if w[-1] == "1":
            delta_w6_1 |= ds

    if delta_global != {0, 21, 34, 55}:
        raise AssertionError(f"Unexpected global delta set: {sorted(delta_global)}")
    if delta_w6_1 != {0, 34}:
        raise AssertionError(f"Unexpected delta set for w6=1: {sorted(delta_w6_1)}")

    # --- Uplift-choice collapse: Xi(w) in {2,3,4} with a hard V-threshold ---
    # Delta set per word and its cardinality Xi(w).
    delta_by_word: Dict[str, List[int]] = {}
    Xi_by_word: Dict[str, int] = {}
    for w, ns in pre.items():
        V = _V_m(w)
        ds_sorted = sorted({int(n - V) for n in ns})
        delta_by_word[w] = ds_sorted
        Xi_by_word[w] = int(len(ds_sorted))

    # For m=6 and domain {0..63}, the truncation boundary is V<=8 iff V+55<=63.
    V_threshold = 8
    words_w6_1 = sorted([w for w in X6 if w[-1] == "1"])
    words_w6_0_V_le = sorted([w for w in X6 if w[-1] == "0" and _V_m(w) <= V_threshold])
    words_w6_0_V_gt = sorted([w for w in X6 if w[-1] == "0" and _V_m(w) > V_threshold])
    if len(words_w6_1) + len(words_w6_0_V_le) + len(words_w6_0_V_gt) != len(X6):
        raise AssertionError("Uplift-choice collapse partition did not cover X6.")
    # Certify constant delta patterns on each region.
    pat_w6_1 = sorted({tuple(delta_by_word[w]) for w in words_w6_1})
    pat_w6_0_V_le = sorted({tuple(delta_by_word[w]) for w in words_w6_0_V_le})
    pat_w6_0_V_gt = sorted({tuple(delta_by_word[w]) for w in words_w6_0_V_gt})
    if pat_w6_1 != [(0, 34)]:
        raise AssertionError(f"Unexpected delta pattern for w6=1: {pat_w6_1}")
    if pat_w6_0_V_gt != [(0, 21, 34)]:
        raise AssertionError(f"Unexpected delta pattern for w6=0 and V>8: {pat_w6_0_V_gt}")
    if pat_w6_0_V_le != [(0, 21, 34, 55)]:
        raise AssertionError(f"Unexpected delta pattern for w6=0 and V<=8: {pat_w6_0_V_le}")

    bdry_pairs: List[Dict[str, object]] = []
    for w in bdry:
        ns = sorted(pre[w])
        V = _V_m(w)
        ds = [n - V for n in ns]
        if len(ns) != 2:
            raise AssertionError(f"Boundary word should have exactly 2 preimages: w={w} pre={ns}")
        if ns[1] - ns[0] != 34:
            raise AssertionError(f"Boundary sheet difference is not 34: w={w} pre={ns}")
        bdry_pairs.append({"w": w, "V6": V, "preimages": ns, "deltas": ds})

    # --- Cross-resolution stability scan (m=6,7,8) for boundary lift patterns (dyadic fold) ---
    bdry_lift_scan: List[Dict[str, object]] = []
    for mm in (6, 7, 8):
        Xm = sorted([word_to_str(w) for w in _golden_words(mm)])
        bdrym = sorted([w for w in Xm if w[0] == "1" and w[-1] == "1"])
        Km = _K_of_m(mm)
        prem: Dict[str, List[int]] = {w: [] for w in Xm}
        for n in range(0, 1 << mm):
            ww = _fold_bin_prefix(n, m=mm, K=Km)
            prem[ww].append(n)
        sizes = [len(prem[w]) for w in bdrym]
        patterns: Dict[str, int] = {}
        for w in bdrym:
            V = _V_m(w)
            ds = sorted({int(n - V) for n in prem[w]})
            key = ",".join(str(x) for x in ds)
            patterns[key] = patterns.get(key, 0) + 1
        bdry_lift_scan.append(
            {
                "m": mm,
                "K_of_m": Km,
                "bdry_count": len(bdrym),
                "preimage_size_min": int(min(sizes)) if sizes else 0,
                "preimage_size_max": int(max(sizes)) if sizes else 0,
                "delta_patterns": dict(sorted(patterns.items())),
            }
        )

    # --- JSON export ---
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(
        json.dumps(
            {
                "m": 6,
                "X6": X6,
                "X6_cyc": cyc,
                "X6_bdry": bdry,
                "C6_orbits_cyc": [
                    {"rep": o.rep, "size": o.size, "weight": o.weight, "words": o.words} for o in orbits
                ],
                "C6_character_decomposition": {
                    "chi_k_definition": "chi_k(rho)=exp(2*pi*i*k/6), k=0..5",
                    "multiplicities_total_m0_to_m5": m_total,
                    "orbit_size_grouping_663_vs_21": {
                        "big_orbit_sizes_sorted": big_sizes,
                        "small_orbit_sizes_sorted": small_sizes,
                        "multiplicities_big_m0_to_m5": m_big,
                        "multiplicities_small_m0_to_m5": m_small,
                    },
                    "induced_module_term_counts": {
                        "Reg_C6": n_reg,
                        "Ind_C2_to_C6_trivial": n_ind_c2,
                        "Ind_C3_to_C6_trivial": n_ind_c3,
                        "trivial": n_triv,
                    },
                },
                "window6_patisalam_9633_partition": {
                    "X6_wt2_cyc_9": cyc_wt2,
                    "X6_wt1_cyc_6": cyc_wt1,
                    "X6_wt0_or_3_cyc_3": cyc_wt0_or_3,
                    "X6_bdry_3": bdry,
                },
                "Fold_bin": {
                    "domain": [0, (1 << m) - 1],
                    "K_of_m": K,
                    "delta_global": sorted(list(delta_global)),
                    "delta_w6_eq_1": sorted(list(delta_w6_1)),
                    "delta_by_word": {w: delta_by_word[w] for w in X6},
                    "Xi_by_word": {w: Xi_by_word[w] for w in X6},
                    "uplift_choice_collapse": {
                        "V_threshold": V_threshold,
                        "w6_eq_1": {
                            "Xi": 2,
                            "delta": [0, 34],
                            "words": words_w6_1,
                        },
                        "w6_eq_0_V_gt_threshold": {
                            "Xi": 3,
                            "delta": [0, 21, 34],
                            "words": words_w6_0_V_gt,
                        },
                        "w6_eq_0_V_le_threshold": {
                            "Xi": 4,
                            "delta": [0, 21, 34, 55],
                            "words": words_w6_0_V_le,
                        },
                    },
                    "boundary_sheet_pairs": bdry_pairs,
                    "boundary_lift_scan_m6_m8": bdry_lift_scan,
                },
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )

    # --- LaTeX: orbit decomposition equation ---
    eq_lines: List[str] = []
    eq_lines.append("% AUTO-GENERATED by scripts/exp_window6_c6_orbit_patisalam_seed.py")
    eq_lines.append("\\[")
    eq_lines.append("\\begin{aligned}")
    eq_lines.append(r"X_6^{\mathrm{cyc}}&=\bigsqcup_{j=1}^{5}\mathcal{O}_j,\qquad (|\mathcal{O}_j|)_{j=1}^{5}=(1,2,3,6,6),\\")
    eq_lines.append(r"\dim \mathbb{R}[X_6^{\mathrm{cyc}}]&=18=1\oplus 2\oplus 3\oplus 6\oplus 6\qquad(\text{orbit spans under the }C_6\text{ action}).")
    eq_lines.append("\\end{aligned}")
    eq_lines.append("\\]")
    eq_lines.append("")
    tex_eq_orbit.parent.mkdir(parents=True, exist_ok=True)
    tex_eq_orbit.write_text("\n".join(eq_lines), encoding="utf-8")

    # --- LaTeX: C6 character decomposition / Fourier multiplicities ---
    def _vec_tex(v: Sequence[int]) -> str:
        return "(" + ",".join(str(int(x)) for x in v) + ")"

    char_lines: List[str] = []
    char_lines.append("% AUTO-GENERATED by scripts/exp_window6_c6_orbit_patisalam_seed.py")
    char_lines.append("\\[")
    char_lines.append("\\begin{aligned}")
    char_lines.append(
        r"\CC[X_6^{\mathrm{cyc}}]"
        r"&\cong "
        + rf"{n_reg}\,\mathrm{{Reg}}_{{C_6}}"
        + r"\ \oplus\ "
        + r"\mathrm{Ind}_{C_2}^{C_6}\ind"
        + r"\ \oplus\ "
        + r"\mathrm{Ind}_{C_3}^{C_6}\ind"
        + r"\ \oplus\ "
        + r"\ind,"
        + r"\\"
    )
    char_lines.append(
        r"\chi_k(\rho)"
        r"&=e^{2\pi i k/6}\ (k=0,\dots,5),\qquad (m_0,m_1,m_2,m_3,m_4,m_5)=" + _vec_tex(m_total) + r",\\"
    )
    char_lines.append(
        r"18=(6\oplus 6\oplus 3)\ \oplus\ (2\oplus 1)"
        r"&=15\oplus 3,\qquad (m_0,\dots,m_5)_{15}="
        + _vec_tex(m_big)
        + r",\quad (m_0,\dots,m_5)_{3}="
        + _vec_tex(m_small)
        + r"."
    )
    char_lines.append("\\end{aligned}")
    char_lines.append("\\]")
    char_lines.append("")
    tex_eq_char.parent.mkdir(parents=True, exist_ok=True)
    tex_eq_char.write_text("\n".join(char_lines), encoding="utf-8")

    # --- LaTeX: orbit table ---
    tab_lines: List[str] = []
    tab_lines.append("% AUTO-GENERATED by scripts/exp_window6_c6_orbit_patisalam_seed.py")
    tab_lines.append("\\begin{table}[H]")
    tab_lines.append("\\centering")
    tab_lines.append("\\small")
    tab_lines.append("\\setlength{\\tabcolsep}{7pt}")
    tab_lines.append("\\renewcommand{\\arraystretch}{1.10}")
    tab_lines.append(
        "\\caption{C6 rotation orbits of the cyclic sector $X_6^{\\mathrm{cyc}}$ (golden-mean legal words with $u_1u_6=0$). "
        "Orbit elements are shown in lexicographic order.}"
    )
    tab_lines.append("\\label{tab:window6_c6_orbit_decomposition}")
    tab_lines.append("\\begin{tabular}{r l r p{0.62\\linewidth}}")
    tab_lines.append("\\toprule")
    tab_lines.append("$|\\mathcal{O}|$ & representative & $\\mathrm{wt}$ & orbit $\\mathcal{O}$\\\\")
    tab_lines.append("\\midrule")
    for o in orbits:
        tab_lines.append(f"{o.size} & \\texttt{{{o.rep}}} & {o.weight} & {_tex_tt_set(o.words)}\\\\")
    tab_lines.append("\\bottomrule")
    tab_lines.append("\\end{tabular}")
    tab_lines.append("\\end{table}")
    tab_lines.append("")
    tex_tab_orbit.parent.mkdir(parents=True, exist_ok=True)
    tex_tab_orbit.write_text("\n".join(tab_lines), encoding="utf-8")

    # --- LaTeX: 9+6+3+3 partition table (weight-layered + boundary) ---
    part_lines: List[str] = []
    part_lines.append("% AUTO-GENERATED by scripts/exp_window6_c6_orbit_patisalam_seed.py")
    part_lines.append("\\begin{table}[H]")
    part_lines.append("\\centering")
    part_lines.append("\\small")
    part_lines.append("\\setlength{\\tabcolsep}{7pt}")
    part_lines.append("\\renewcommand{\\arraystretch}{1.10}")
    part_lines.append(
        "\\caption{Rigid four-block partition of $X_6$ induced by the cyclic/boundary split and Hamming-weight layers of $X_6^{\\mathrm{cyc}}$.}"
    )
    part_lines.append("\\label{tab:window6_patisalam_9633_partition}")
    part_lines.append("\\begin{tabular}{l r p{0.68\\linewidth}}")
    part_lines.append("\\toprule")
    part_lines.append("block & size & words\\\\")
    part_lines.append("\\midrule")
    part_lines.append(
        r"$X^{(2)}_6:=\{w\in X_6^{\mathrm{cyc}}:\ \mathrm{wt}(w)=2\}$"
        + f" & {len(cyc_wt2)} & {_tex_tt_set(cyc_wt2)}\\\\"
    )
    part_lines.append(
        r"$X^{(1)}_6:=\{w\in X_6^{\mathrm{cyc}}:\ \mathrm{wt}(w)=1\}$"
        + f" & {len(cyc_wt1)} & {_tex_tt_set(cyc_wt1)}\\\\"
    )
    part_lines.append(
        r"$X^{(L)}_6:=\{w\in X_6^{\mathrm{cyc}}:\ \mathrm{wt}(w)\in\{0,3\}\}$"
        + f" & {len(cyc_wt0_or_3)} & {_tex_tt_set(cyc_wt0_or_3)}\\\\"
    )
    part_lines.append(
        r"$X^{(R)}_6:=X_6^{\mathrm{bdry}}$" + f" & {len(bdry)} & {_tex_tt_set(bdry)}\\\\"
    )
    part_lines.append("\\bottomrule")
    part_lines.append("\\end{tabular}")
    part_lines.append("\\end{table}")
    part_lines.append("")
    tex_tab_partition.parent.mkdir(parents=True, exist_ok=True)
    tex_tab_partition.write_text("\n".join(part_lines), encoding="utf-8")

    # --- LaTeX: uplift delta set equation (dyadic fold) ---
    delta_tex = ",\\ ".join(str(x) for x in sorted(delta_global))
    delta_w6_1_tex = ",\\ ".join(str(x) for x in sorted(delta_w6_1))
    eqd_lines: List[str] = []
    eqd_lines.append("% AUTO-GENERATED by scripts/exp_window6_c6_orbit_patisalam_seed.py")
    eqd_lines.append("\\[")
    eqd_lines.append("\\begin{aligned}")
    eqd_lines.append(r"\Delta_6&:=\{\,n-V_6(\mathrm{Fold}^{\mathrm{bin}}_6(n)):\ 0\le n\le 63\,\}=" + f"\\{{{delta_tex}\\}},\\\\")
    eqd_lines.append(r"w_6=1\ &\Longrightarrow\ \{\,n-V_6(w):\ n\in (\mathrm{Fold}^{\mathrm{bin}}_6)^{-1}(w)\,\}=" + f"\\{{{delta_w6_1_tex}\\}}.")
    eqd_lines.append("\\end{aligned}")
    eqd_lines.append("\\]")
    eqd_lines.append("")
    tex_eq_delta.parent.mkdir(parents=True, exist_ok=True)
    tex_eq_delta.write_text("\n".join(eqd_lines), encoding="utf-8")

    # --- LaTeX: uplift-choice collapse table (dyadic fold, m=6) ---
    def _tt_words(words: Sequence[str]) -> str:
        # Use \texttt{...} with commas, no surrounding braces (table cell).
        return ",\\ ".join([f"\\texttt{{{w}}}" for w in words])

    tabc_lines: List[str] = []
    tabc_lines.append("% AUTO-GENERATED by scripts/exp_window6_c6_orbit_patisalam_seed.py")
    tabc_lines.append("\\begin{table}[H]")
    tabc_lines.append("\\centering")
    tabc_lines.append("\\small")
    tabc_lines.append("\\setlength{\\tabcolsep}{7pt}")
    tabc_lines.append("\\renewcommand{\\arraystretch}{1.10}")
    tabc_lines.append(
        "\\caption{Dyadic uplift-choice collapse at $m=6$ for $\\mathrm{Fold}^{\\mathrm{bin}}_6$: "
        "the uplift-delta set $\\Delta(w)=\\{n-V_6(w): n\\in (\\mathrm{Fold}^{\\mathrm{bin}}_6)^{-1}(w)\\}$ "
        "has cardinality $\\Xi(w)\\in\\{2,3,4\\}$, with a hard threshold at $V_6(w)\\le 8$ imposed by the finite domain $\\{0,\\dots,63\\}$.}"
    )
    tabc_lines.append("\\label{tab:fold6_bin_uplift_choice_collapse}")
    tabc_lines.append("\\begin{tabular}{l r l p{0.54\\linewidth}}")
    tabc_lines.append("\\toprule")
    tabc_lines.append("condition & $\\Xi(w)$ & $\\Delta(w)$ & words\\\\")
    tabc_lines.append("\\midrule")
    tabc_lines.append(
        r"$w_6=0,\ V_6(w)\le 8$"
        + " & 4 & $\\{0,21,34,55\\}$ & "
        + _tt_words(words_w6_0_V_le)
        + "\\\\"
    )
    tabc_lines.append(
        r"$w_6=0,\ V_6(w)> 8$"
        + " & 3 & $\\{0,21,34\\}$ & "
        + _tt_words(words_w6_0_V_gt)
        + "\\\\"
    )
    tabc_lines.append(r"$w_6=1$" + " & 2 & $\\{0,34\\}$ & " + _tt_words(words_w6_1) + "\\\\")
    tabc_lines.append("\\bottomrule")
    tabc_lines.append("\\end{tabular}")
    tabc_lines.append("\\end{table}")
    tabc_lines.append("")
    tex_tab_choice_collapse.parent.mkdir(parents=True, exist_ok=True)
    tex_tab_choice_collapse.write_text("\n".join(tabc_lines), encoding="utf-8")

    # --- LaTeX: boundary sheet pairs table ---
    tab2_lines: List[str] = []
    tab2_lines.append("% AUTO-GENERATED by scripts/exp_window6_c6_orbit_patisalam_seed.py")
    tab2_lines.append("\\begin{table}[H]")
    tab2_lines.append("\\centering")
    tab2_lines.append("\\small")
    tab2_lines.append("\\setlength{\\tabcolsep}{10pt}")
    tab2_lines.append("\\renewcommand{\\arraystretch}{1.10}")
    tab2_lines.append(
        "\\caption{Two-sheet dyadic lift for the window-6 boundary sector $X_6^{\\mathrm{bdry}}$: "
        "each boundary word has exactly two preimages under $\\mathrm{Fold}^{\\mathrm{bin}}_6$, differing by $34=F_9$.}"
    )
    tab2_lines.append("\\label{tab:fold6_boundary_sheet_pairs}")
    tab2_lines.append("\\begin{tabular}{l r l}")
    tab2_lines.append("\\toprule")
    tab2_lines.append("$w\\in X_6^{\\mathrm{bdry}}$ & $V_6(w)$ & $(\\mathrm{Fold}^{\\mathrm{bin}}_6)^{-1}(w)$\\\\")
    tab2_lines.append("\\midrule")
    for row in bdry_pairs:
        w = str(row["w"])
        V = int(row["V6"])
        ns = [int(x) for x in row["preimages"]]  # type: ignore[arg-type]
        tab2_lines.append(f"\\texttt{{{w}}} & {V} & $\\{{{ns[0]},{ns[1]}\\}}$\\\\")
    tab2_lines.append("\\bottomrule")
    tab2_lines.append("\\end{tabular}")
    tab2_lines.append("\\end{table}")
    tab2_lines.append("")
    tex_tab_bdry.parent.mkdir(parents=True, exist_ok=True)
    tex_tab_bdry.write_text("\n".join(tab2_lines), encoding="utf-8")

    # --- LaTeX: boundary lift stability (m=6..8) ---
    stab_lines: List[str] = []
    stab_lines.append("% AUTO-GENERATED by scripts/exp_window6_c6_orbit_patisalam_seed.py")
    stab_lines.append("\\begin{table}[H]")
    stab_lines.append("\\centering")
    stab_lines.append("\\small")
    stab_lines.append("\\setlength{\\tabcolsep}{10pt}")
    stab_lines.append("\\renewcommand{\\arraystretch}{1.10}")
    stab_lines.append(
        "\\caption{Dyadic boundary-sector lift patterns for $\\mathrm{Fold}^{\\mathrm{bin}}_m$ at $m\\in\\{6,7,8\\}$: "
        "for each $m$, all boundary words share the same uplift-delta pattern "
        "$\\{n-V_m(w): n\\in (\\mathrm{Fold}^{\\mathrm{bin}}_m)^{-1}(w)\\}$.}"
    )
    stab_lines.append("\\label{tab:foldbin_boundary_lift_m6_m8}")
    stab_lines.append("\\begin{tabular}{r r r l}")
    stab_lines.append("\\toprule")
    stab_lines.append("$m$ & $|X_m^{\\mathrm{bdry}}|$ & $\\#(\\mathrm{Fold}^{\\mathrm{bin}}_m)^{-1}(w)$ & uplift deltas\\\\")
    stab_lines.append("\\midrule")
    for row in bdry_lift_scan:
        mm = int(row["m"])
        cnt = int(row["bdry_count"])
        smin = int(row["preimage_size_min"])
        smax = int(row["preimage_size_max"])
        size_tex = str(smin) if smin == smax else f"{smin}\\text{{--}}{smax}"
        patterns = row["delta_patterns"]
        if not isinstance(patterns, dict) or len(patterns) == 0:
            raise AssertionError("Missing delta_patterns in boundary lift scan.")
        if len(patterns) == 1:
            k = next(iter(patterns.keys()))
            pat_tex = f"\\{{{k.replace(',',',\\ ')}\\}}"
        else:
            parts: List[str] = []
            for k, v in patterns.items():
                parts.append(f"\\{{{k.replace(',',',\\ ')}\\}}\\times {v}")
            pat_tex = ";\\ ".join(parts)
        stab_lines.append(f"{mm} & {cnt} & {size_tex} & ${pat_tex}$\\\\")
    stab_lines.append("\\bottomrule")
    stab_lines.append("\\end{tabular}")
    stab_lines.append("\\end{table}")
    stab_lines.append("")
    tex_tab_bdry_stability.parent.mkdir(parents=True, exist_ok=True)
    tex_tab_bdry_stability.write_text("\n".join(stab_lines), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Window-6 C6 orbit + dyadic boundary-sheet audit artifacts.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "window6_c6_orbit_patisalam_seed.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-eq-orbit",
        type=str,
        default=str(generated_dir() / "eq_window6_c6_orbit_decomposition.tex"),
        help="Output LaTeX equation fragment path (orbit decomposition).",
    )
    parser.add_argument(
        "--tex-eq-char",
        type=str,
        default=str(generated_dir() / "eq_window6_c6_character_decomposition.tex"),
        help="Output LaTeX equation fragment path (C6 character decomposition / Fourier multiplicities).",
    )
    parser.add_argument(
        "--tex-tab-orbit",
        type=str,
        default=str(generated_dir() / "tab_window6_c6_orbit_decomposition.tex"),
        help="Output LaTeX table fragment path (orbit decomposition).",
    )
    parser.add_argument(
        "--tex-tab-partition",
        type=str,
        default=str(generated_dir() / "tab_window6_patisalam_9633_partition.tex"),
        help="Output LaTeX table fragment path (rigid 9+6+3+3 partition of X6).",
    )
    parser.add_argument(
        "--tex-eq-delta",
        type=str,
        default=str(generated_dir() / "eq_fold6_bin_uplift_delta_set.tex"),
        help="Output LaTeX equation fragment path (dyadic uplift delta set).",
    )
    parser.add_argument(
        "--tex-tab-choice-collapse",
        type=str,
        default=str(generated_dir() / "tab_fold6_bin_uplift_choice_collapse.tex"),
        help="Output LaTeX table fragment path (dyadic uplift-choice collapse at m=6).",
    )
    parser.add_argument(
        "--tex-tab-bdry",
        type=str,
        default=str(generated_dir() / "tab_fold6_boundary_sheet_pairs.tex"),
        help="Output LaTeX table fragment path (boundary sheet pairs).",
    )
    parser.add_argument(
        "--tex-tab-bdry-stability",
        type=str,
        default=str(generated_dir() / "tab_foldbin_boundary_lift_m6_m8.tex"),
        help="Output LaTeX table fragment path (boundary lift stability scan for m=6..8).",
    )
    args = parser.parse_args()

    write_outputs(
        json_out=Path(args.json_out),
        tex_eq_orbit=Path(args.tex_eq_orbit),
        tex_eq_char=Path(args.tex_eq_char),
        tex_tab_orbit=Path(args.tex_tab_orbit),
        tex_tab_partition=Path(args.tex_tab_partition),
        tex_eq_delta=Path(args.tex_eq_delta),
        tex_tab_choice_collapse=Path(args.tex_tab_choice_collapse),
        tex_tab_bdry=Path(args.tex_tab_bdry),
        tex_tab_bdry_stability=Path(args.tex_tab_bdry_stability),
    )
    print(f"[window6-c6-orbit] wrote {args.json_out}", flush=True)
    print(f"[window6-c6-orbit] wrote {args.tex_eq_orbit}", flush=True)
    print(f"[window6-c6-orbit] wrote {args.tex_eq_char}", flush=True)
    print(f"[window6-c6-orbit] wrote {args.tex_tab_orbit}", flush=True)
    print(f"[window6-c6-orbit] wrote {args.tex_tab_partition}", flush=True)
    print(f"[window6-c6-orbit] wrote {args.tex_eq_delta}", flush=True)
    print(f"[window6-c6-orbit] wrote {args.tex_tab_choice_collapse}", flush=True)
    print(f"[window6-c6-orbit] wrote {args.tex_tab_bdry}", flush=True)
    print(f"[window6-c6-orbit] wrote {args.tex_tab_bdry_stability}", flush=True)
    print("[window6-c6-orbit] done", flush=True)


if __name__ == "__main__":
    main()

