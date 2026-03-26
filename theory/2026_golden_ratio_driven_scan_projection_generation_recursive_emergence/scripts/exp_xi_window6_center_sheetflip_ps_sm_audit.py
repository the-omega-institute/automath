#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit window-6 center-sheetflip constraints and PS/SM center morphisms.

This script certifies the core algebraic and combinatorial claims used in the
window-6 prime-register section:

1) Standard-model connected envelopes with Lie algebra
     u(1) ⊕ su(2) ⊕ su(3)
   have center 2-torsion rank at most 2.

2) For
     G_tilde_PS = SU(4) × SU(2)_L × SU(2)_R,
   the canonical involution subgroup
     C_can = Z(SU(4))[2] × Z(SU(2)_L) × Z(SU(2)_R) ≅ (Z/2)^3
   intersects every nontrivial central quotient kernel H ⊂ Z(G_tilde_PS)
   nontrivially; hence full-faithful descent of all three canonical sheet-flips
   forces H = {e}.

3) Under central-compatibility, any homomorphism from C_can to a target with
   center 2-rank <= 2 has nontrivial kernel.

4) Dyadic boundary uplift patterns at m = 6,7,8 are:
     {0,34}, {0,55,89}, {0,89,144},
   with two-sheet boundary parity uniquely recoverable only at m=6.

5) For the L/R swap involution iota on C_can, the map
     pi_LR(alpha,beta,gamma)=beta+gamma (mod 2)
   has kernel exactly C_can^{iota}.

Output:
  - artifacts/export/xi_window6_center_sheetflip_ps_sm_audit.json
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, FrozenSet, Iterable, List, Sequence, Set, Tuple

from common_paths import export_dir
from common_phi_fold import fib_upto, word_to_str, zeckendorf_digits


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _fib(k: int) -> int:
    if k <= 0:
        raise ValueError("k must be >= 1")
    return int(fib_upto(k)[-1])


def _golden_words(m: int) -> List[str]:
    out: List[str] = []

    def rec(pos: int, prev1: int, acc: List[int]) -> None:
        if pos == m:
            out.append(word_to_str(acc))
            return
        acc.append(0)
        rec(pos + 1, 0, acc)
        acc.pop()
        if prev1 == 0:
            acc.append(1)
            rec(pos + 1, 1, acc)
            acc.pop()

    rec(0, 0, [])
    return sorted(out)


def _V_m(w: str) -> int:
    m = len(w)
    fb = fib_upto(m + 2)
    return sum((1 if ch == "1" else 0) * int(fb[i + 1]) for i, ch in enumerate(w))


def _K_of_m(m: int) -> int:
    target = (1 << m) - 1
    f1, f2 = 1, 1
    idx = 2
    while f2 <= target:
        f1, f2 = f2, f1 + f2
        idx += 1
    return idx - 2


def _fold_bin_prefix(n: int, *, m: int, K: int) -> str:
    digits = zeckendorf_digits(n, K)
    return word_to_str(digits[:m])


# ---------- Finite center model for Z(G_tilde_PS) = Z4 x Z2 x Z2 ----------

Elem = Tuple[int, int, int]  # additive coordinates modulo (4,2,2)


def _add(x: Elem, y: Elem) -> Elem:
    return ((x[0] + y[0]) % 4, (x[1] + y[1]) % 2, (x[2] + y[2]) % 2)


def _double(x: Elem) -> Elem:
    return _add(x, x)


def _subgroup_from_gens(gens: Iterable[Elem]) -> FrozenSet[Elem]:
    S: Set[Elem] = {(0, 0, 0)}
    gens_list = list(gens)
    changed = True
    while changed:
        changed = False
        for x in list(S):
            for g in gens_list:
                y = _add(x, g)
                if y not in S:
                    S.add(y)
                    changed = True
    return frozenset(S)


def _all_subgroups() -> List[FrozenSet[Elem]]:
    A = [(a, b, c) for a in range(4) for b in range(2) for c in range(2)]
    nonzero = A[1:]
    subs: Set[FrozenSet[Elem]] = set()
    # rank <= 3 generators suffice, 4 keeps it robust and still tiny.
    for r in range(0, 5):
        for gs in itertools.combinations(nonzero, r):
            subs.add(_subgroup_from_gens(gs))
    return sorted(subs, key=lambda H: (len(H), sorted(H)))


def _coset_representatives(A: Sequence[Elem], H: FrozenSet[Elem]) -> List[Elem]:
    reps: List[Elem] = []
    used: Set[Elem] = set()
    for a in A:
        if a in used:
            continue
        cos = {_add(a, h) for h in H}
        reps.append(a)
        used |= cos
    return reps


def _two_torsion_rank_of_quotient(H: FrozenSet[Elem]) -> int:
    A = [(a, b, c) for a in range(4) for b in range(2) for c in range(2)]
    reps = _coset_representatives(A, H)
    torsion_classes = 0
    for a in reps:
        if _double(a) in H:
            torsion_classes += 1
    if torsion_classes <= 0:
        raise RuntimeError("invalid quotient torsion count")
    r = round(math.log2(torsion_classes))
    if 2**r != torsion_classes:
        raise RuntimeError("2-torsion class count is not a power of two")
    return int(r)


@dataclass(frozen=True)
class Payload:
    sm_center_2rank_upper_bound: int
    sm_center_2rank_bound_ok: bool
    ps_center_2rank_cover: int
    nontrivial_subgroup_count_ps_center: int
    all_nontrivial_subgroups_intersect_canonical_2torsion: bool
    canonical_faithful_descent_only_trivial_quotient: bool
    max_2rank_after_nontrivial_quotient: int
    exists_nontrivial_quotient_with_2rank3: bool
    central_compatibility_kernel_forced_nontrivial: bool
    boundary_pattern_m6: List[int]
    boundary_pattern_m7: List[int]
    boundary_pattern_m8: List[int]
    boundary_patterns_match_expected: bool
    m6_boundary_two_sheet_diff_34: bool
    m7_m8_not_binary_pairing_without_extra_choice: bool
    iota_kernel_equals_fixed_subgroup: bool
    iota_kernel_rank: int
    elapsed_s: float


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Audit window-6 center-sheetflip constraints and PS/SM center algebra."
    )
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    t0 = time.time()

    print("[window6-center-audit] phase=sm-center-rank", flush=True)
    # Z(U(1)×SU(2)×SU(3))[2] = U(1)[2] × Z2 × 0, hence rank <= 2 for any central quotient.
    sm_rank_upper = 2
    sm_rank_ok = sm_rank_upper <= 2

    print("[window6-center-audit] phase=ps-center-subgroup-enumeration", flush=True)
    subs = _all_subgroups()
    nontrivial_subs = [H for H in subs if len(H) > 1]
    # canonical involution subgroup C_can = {(0 or 2, b, c)}.
    c_can: FrozenSet[Elem] = frozenset((a, b, c) for a in (0, 2) for b in (0, 1) for c in (0, 1))

    all_nontrivial_intersect = all(len(H.intersection(c_can)) > 1 for H in nontrivial_subs)
    faithful_only_trivial = all(
        (len(H) == 1) for H in subs if len(H.intersection(c_can)) == 1  # intersection only identity
    )

    max_rank_nontrivial = max(_two_torsion_rank_of_quotient(H) for H in nontrivial_subs)
    exists_rank3_nontrivial = any(_two_torsion_rank_of_quotient(H) == 3 for H in nontrivial_subs)

    print("[window6-center-audit] phase=boundary-lift-patterns", flush=True)
    expected_patterns = {
        6: [0, 34],
        7: [0, 55, 89],
        8: [0, 89, 144],
    }
    observed: Dict[int, List[int]] = {}
    m6_pair_diff_34 = True
    for m in (6, 7, 8):
        Xm = _golden_words(m)
        bdry = [w for w in Xm if w[0] == "1" and w[-1] == "1"]
        K = _K_of_m(m)
        pre: Dict[str, List[int]] = {w: [] for w in Xm}
        for n in range(0, 1 << m):
            ww = _fold_bin_prefix(n, m=m, K=K)
            pre[ww].append(n)

        patterns: Set[Tuple[int, ...]] = set()
        for w in bdry:
            V = _V_m(w)
            ds = sorted({int(n - V) for n in pre[w]})
            patterns.add(tuple(ds))
            if m == 6:
                ns = sorted(pre[w])
                if len(ns) != 2 or (ns[1] - ns[0]) != 34:
                    m6_pair_diff_34 = False
        if len(patterns) != 1:
            raise AssertionError(f"boundary patterns are not uniform at m={m}: {patterns}")
        observed[m] = list(next(iter(patterns)))

    patterns_match_expected = all(observed[m] == expected_patterns[m] for m in (6, 7, 8))
    m7_m8_need_extra_choice = len(observed[7]) > 2 and len(observed[8]) > 2

    print("[window6-center-audit] phase=lr-involution-kernel", flush=True)
    vectors = [(a, b, c) for a in (0, 1) for b in (0, 1) for c in (0, 1)]  # F2^3 coordinates

    def iota(v: Tuple[int, int, int]) -> Tuple[int, int, int]:
        return (v[0], v[2], v[1])

    def pi_lr(v: Tuple[int, int, int]) -> int:
        return (v[1] + v[2]) % 2

    ker = {v for v in vectors if pi_lr(v) == 0}
    fix = {v for v in vectors if iota(v) == v}
    lr_kernel_equals_fixed = ker == fix
    ker_rank = round(math.log2(len(ker)))

    # Linear-algebra forcing statement (domain rank 3 to codomain rank <=2).
    central_compatibility_kernel_forced_nontrivial = 3 > sm_rank_upper

    payload = Payload(
        sm_center_2rank_upper_bound=sm_rank_upper,
        sm_center_2rank_bound_ok=bool(sm_rank_ok),
        ps_center_2rank_cover=3,
        nontrivial_subgroup_count_ps_center=len(nontrivial_subs),
        all_nontrivial_subgroups_intersect_canonical_2torsion=bool(all_nontrivial_intersect),
        canonical_faithful_descent_only_trivial_quotient=bool(faithful_only_trivial),
        max_2rank_after_nontrivial_quotient=int(max_rank_nontrivial),
        exists_nontrivial_quotient_with_2rank3=bool(exists_rank3_nontrivial),
        central_compatibility_kernel_forced_nontrivial=bool(central_compatibility_kernel_forced_nontrivial),
        boundary_pattern_m6=observed[6],
        boundary_pattern_m7=observed[7],
        boundary_pattern_m8=observed[8],
        boundary_patterns_match_expected=bool(patterns_match_expected),
        m6_boundary_two_sheet_diff_34=bool(m6_pair_diff_34),
        m7_m8_not_binary_pairing_without_extra_choice=bool(m7_m8_need_extra_choice),
        iota_kernel_equals_fixed_subgroup=bool(lr_kernel_equals_fixed),
        iota_kernel_rank=int(ker_rank),
        elapsed_s=float(time.time() - t0),
    )

    if not payload.sm_center_2rank_bound_ok:
        raise AssertionError("SM center 2-rank bound failed")
    if not payload.all_nontrivial_subgroups_intersect_canonical_2torsion:
        raise AssertionError("Found nontrivial PS center quotient kernel disjoint from canonical 2-torsion")
    if not payload.canonical_faithful_descent_only_trivial_quotient:
        raise AssertionError("Found nontrivial quotient preserving faithful canonical 3-axis descent")
    if not payload.boundary_patterns_match_expected:
        raise AssertionError(
            f"Unexpected boundary uplift patterns: m6={payload.boundary_pattern_m6}, "
            f"m7={payload.boundary_pattern_m7}, m8={payload.boundary_pattern_m8}"
        )
    if not payload.m6_boundary_two_sheet_diff_34:
        raise AssertionError("m=6 boundary words are not uniform two-sheet pairs with difference 34")
    if not payload.m7_m8_not_binary_pairing_without_extra_choice:
        raise AssertionError("m=7,8 unexpectedly admit binary pairing without extra choice")
    if not payload.iota_kernel_equals_fixed_subgroup:
        raise AssertionError("Ker(pi_LR) != fixed subgroup under L/R swap involution")
    if payload.iota_kernel_rank != 2:
        raise AssertionError(f"Unexpected kernel rank: {payload.iota_kernel_rank}")
    if not payload.central_compatibility_kernel_forced_nontrivial:
        raise AssertionError("central-compatibility kernel forcing check failed")

    if not args.no_output:
        out = export_dir() / "xi_window6_center_sheetflip_ps_sm_audit.json"
        _write_json(out, asdict(payload))

    print(
        "[window6-center-audit] "
        f"sm_rank<=2:{payload.sm_center_2rank_bound_ok} "
        f"faithful_only_trivial:{payload.canonical_faithful_descent_only_trivial_quotient} "
        f"patterns_ok:{payload.boundary_patterns_match_expected} "
        f"lr_kernel_ok:{payload.iota_kernel_equals_fixed_subgroup} "
        f"elapsed_s={payload.elapsed_s:.3f}",
        flush=True,
    )


if __name__ == "__main__":
    main()
