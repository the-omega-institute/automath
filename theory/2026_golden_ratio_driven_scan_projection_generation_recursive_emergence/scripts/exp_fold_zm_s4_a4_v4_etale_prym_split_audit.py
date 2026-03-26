#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the subgroup tower V4 < A4 < S4 for the regular S4 cover with branch type
one order-4 inertia and five order-2 inertias.

This script performs finite, explicit checks:
  - subgroup chain and quotient sizes,
  - inertia-intersection criterion proving etaleness of X/V4 -> X/A4,
  - Riemann--Hurwitz genera via branch-cycle action on cosets for
    X, X/A4, X/V4, X/D4,
  - consistency identities for Prym dimension and Jacobian splitting dimensions.

Output:
  - artifacts/export/fold_zm_s4_a4_v4_etale_prym_split_audit.json
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

from sympy.combinatorics import Permutation, PermutationGroup

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _perm_str(p: Permutation) -> str:
    return str(p)


def _group_elements(G: PermutationGroup) -> List[Permutation]:
    return list(G.generate_dimino())


def _right_coset_reps(G: PermutationGroup, H: PermutationGroup) -> Tuple[List[Permutation], List[Permutation]]:
    G_elems = _group_elements(G)
    H_elems = _group_elements(H)
    remaining = list(G_elems)
    reps: List[Permutation] = []
    while remaining:
        r = remaining[0]
        reps.append(r)
        coset = {r * h for h in H_elems}
        remaining = [g for g in remaining if g not in coset]
    return reps, H_elems


def _coset_action_cycle_lengths(
    G: PermutationGroup, H: PermutationGroup, s: Permutation
) -> Tuple[int, List[int], int]:
    """
    Right action on G/H: gH -> (g*s)H.
    Returns (degree, cycle_lengths_desc, ramification_contribution=d-#cycles).
    """
    reps, H_elems = _right_coset_reps(G, H)
    d = len(reps)
    image: List[int] = []
    for r in reps:
        target = r * s
        idx = -1
        for j, rep in enumerate(reps):
            # target in rep*H  <=>  rep^{-1}*target in H
            if any(rep * h == target for h in H_elems):
                idx = j
                break
        if idx < 0:
            raise RuntimeError("Failed to resolve coset action index.")
        image.append(idx)

    seen = [False] * d
    cycle_lengths: List[int] = []
    for i in range(d):
        if seen[i]:
            continue
        cur = i
        length = 0
        while not seen[cur]:
            seen[cur] = True
            length += 1
            cur = image[cur]
        cycle_lengths.append(length)
    cycle_lengths.sort(reverse=True)
    contribution = d - len(cycle_lengths)
    return d, cycle_lengths, contribution


@dataclass(frozen=True)
class BranchActionRow:
    branch_index: int
    generator: str
    order: int
    cycle_lengths: List[int]
    contribution: int


@dataclass(frozen=True)
class QuotientGenusRow:
    subgroup: str
    subgroup_order: int
    degree_to_base: int
    total_ramification: int
    genus: int
    branch_actions: List[BranchActionRow]


def _genus_from_branch_cycles(
    G: PermutationGroup,
    H: PermutationGroup,
    branch_generators: Sequence[Permutation],
    subgroup_name: str,
) -> QuotientGenusRow:
    d = G.order() // H.order()
    rows: List[BranchActionRow] = []
    total_ram = 0
    for i, s in enumerate(branch_generators, start=1):
        d_i, lens, contrib = _coset_action_cycle_lengths(G, H, s)
        if d_i != d:
            raise RuntimeError("Degree mismatch in branch action.")
        total_ram += contrib
        rows.append(
            BranchActionRow(
                branch_index=int(i),
                generator=_perm_str(s),
                order=int(s.order()),
                cycle_lengths=[int(v) for v in lens],
                contribution=int(contrib),
            )
        )
    # Riemann--Hurwitz for quotient curve Y=X/H over P1:
    # 2g(Y)-2 = -2d + total_ramification
    two_g_minus_two = -2 * int(d) + int(total_ram)
    if two_g_minus_two % 2 != 0:
        raise RuntimeError("Parity failure in genus computation.")
    genus = (two_g_minus_two + 2) // 2
    return QuotientGenusRow(
        subgroup=subgroup_name,
        subgroup_order=int(H.order()),
        degree_to_base=int(d),
        total_ramification=int(total_ram),
        genus=int(genus),
        branch_actions=rows,
    )


def main() -> None:
    # Work in degree-4 permutation model on {0,1,2,3}.
    id4 = Permutation([0, 1, 2, 3])
    c4 = Permutation(0, 1, 2, 3, size=4)
    t01 = Permutation(0, 1, size=4)

    v12_34 = Permutation(0, 1, size=4) * Permutation(2, 3, size=4)
    v13_24 = Permutation(0, 2, size=4) * Permutation(1, 3, size=4)
    v14_23 = Permutation(0, 3, size=4) * Permutation(1, 2, size=4)

    S4 = PermutationGroup([c4, t01])
    A4 = PermutationGroup([Permutation(0, 1, 2, size=4), v12_34])
    V4 = PermutationGroup([v12_34, v13_24])
    D4 = PermutationGroup([v12_34, v13_24, t01])
    H1 = PermutationGroup([id4])

    # Branch generators with relation product=1 (left-to-right multiplication):
    # one inertia of order 4 and five inertia generators of order 2.
    #
    # This explicit tuple is chosen to satisfy simultaneously:
    #   (i) monodromy generation = S4,
    #   (ii) genus profile g(X)=16, g(X/A4)=2, g(X/V4)=4, g(X/D4)=1.
    g_inf = c4
    t01 = Permutation(0, 1, size=4)
    t02 = Permutation(0, 2, size=4)
    t03 = Permutation(0, 3, size=4)
    t12 = Permutation(1, 2, size=4)
    branch = [~g_inf, t01, t01, t02, t03, t12]

    prod = id4
    for g in branch:
        prod = prod * g
    relation_ok = prod == id4

    monodromy = PermutationGroup(list(branch))
    monodromy_ok = monodromy.order() == S4.order()

    subgroup_checks = {
        "orders": {
            "S4": int(S4.order()),
            "A4": int(A4.order()),
            "V4": int(V4.order()),
            "D4": int(D4.order()),
        },
        "normality": {
            "V4_normal_in_A4": bool(V4.is_normal(A4)),
            "A4_normal_in_S4": bool(A4.is_normal(S4)),
            "V4_normal_in_S4": bool(V4.is_normal(S4)),
        },
        "quotient_sizes": {
            "A4_over_V4": int(A4.order() // V4.order()),
            "S4_over_A4": int(S4.order() // A4.order()),
        },
    }

    # Inertia image test for etaleness of X/V4 -> X/A4.
    I2 = PermutationGroup([t01])
    I4 = PermutationGroup([c4])
    inter_I2_A4 = [g for g in _group_elements(I2) if A4.contains(g)]
    inter_I4_A4 = [g for g in _group_elements(I4) if A4.contains(g)]
    image_I2_trivial = all(V4.contains(g) for g in inter_I2_A4)
    image_I4_trivial = all(V4.contains(g) for g in inter_I4_A4)
    etale_cubic_ok = image_I2_trivial and image_I4_trivial

    # Genus data from branch-cycle actions.
    row_X = _genus_from_branch_cycles(S4, H1, branch, "1")
    row_XA = _genus_from_branch_cycles(S4, A4, branch, "A4")
    row_XV = _genus_from_branch_cycles(S4, V4, branch, "V4")
    row_E = _genus_from_branch_cycles(S4, D4, branch, "D4")

    # Derived checks for conclusions in the A4/V4 tower.
    gX = row_X.genus
    gXA = row_XA.genus
    gXV = row_XV.genus
    gE = row_E.genus

    # étale degree-3 formula: g(XV) = 3(g(XA)-1)+1
    etale_genus_formula_ok = gXV == 3 * (gXA - 1) + 1

    # Degree-2 quotient XV -> E ramification degree (from RH).
    # 2gXV-2 = 2*(2gE-2) + R
    ram_deg_xv_to_e = (2 * gXV - 2) - 2 * (2 * gE - 2)

    # Prym/Jacobian dimensional consistency.
    dim_prym = gXV - gXA
    jac_split_dim_ok = gXV == gXA + 2 * gE
    polarization_13_kernel = (1 * 3) ** 2

    checks = {
        "branch_relation_identity": bool(relation_ok),
        "monodromy_is_S4": bool(monodromy_ok),
        "subgroup_chain_ok": bool(
            subgroup_checks["normality"]["V4_normal_in_A4"]
            and subgroup_checks["normality"]["A4_normal_in_S4"]
            and subgroup_checks["quotient_sizes"]["A4_over_V4"] == 3
            and subgroup_checks["quotient_sizes"]["S4_over_A4"] == 2
        ),
        "etale_cubic_ok": bool(etale_cubic_ok),
        "gX_is_16": bool(gX == 16),
        "gXA_is_2": bool(gXA == 2),
        "gXV_is_4": bool(gXV == 4),
        "gE_is_1": bool(gE == 1),
        "etale_genus_formula_ok": bool(etale_genus_formula_ok),
        "dim_prym_is_2": bool(dim_prym == 2),
        "jacobian_dimension_split_ok": bool(jac_split_dim_ok),
        "xv_to_e_ramification_degree_is_6": bool(ram_deg_xv_to_e == 6),
    }
    ok = all(checks.values())

    payload: Dict[str, object] = {
        "ok": bool(ok),
        "checks": checks,
        "groups": subgroup_checks,
        "branch_profile": {
            "generators": [_perm_str(g) for g in branch],
            "orders": [int(g.order()) for g in branch],
            "one_order_4_and_five_order_2": bool(
                sorted(int(g.order()) for g in branch) == [2, 2, 2, 2, 2, 4]
            ),
        },
        "etale_inertia_test": {
            "intersection_I2_A4": [_perm_str(g) for g in inter_I2_A4],
            "intersection_I4_A4": [_perm_str(g) for g in inter_I4_A4],
            "image_I2_trivial_in_A4_over_V4": bool(image_I2_trivial),
            "image_I4_trivial_in_A4_over_V4": bool(image_I4_trivial),
        },
        "quotient_genera": {
            "X_over_P1": asdict(row_X),
            "X_A_over_P1": asdict(row_XA),
            "X_V_over_P1": asdict(row_XV),
            "X_D4_over_P1": asdict(row_E),
        },
        "derived": {
            "gX": int(gX),
            "gXA": int(gXA),
            "gXV": int(gXV),
            "gE": int(gE),
            "dim_prym_XV_over_XA": int(dim_prym),
            "xv_to_e_ramification_degree": int(ram_deg_xv_to_e),
            "polarization_type_candidate": "(1,3)",
            "polarization_kernel_size_for_(1,3)": int(polarization_13_kernel),
            "jacobian_dimension_identity_gXV_equals_gXA_plus_2gE": bool(jac_split_dim_ok),
        },
    }

    out_path = export_dir() / "fold_zm_s4_a4_v4_etale_prym_split_audit.json"
    _write_json(out_path, payload)
    print(f"[fold-zm-s4-a4-v4-etale-prym-split] ok={ok} wrote={out_path}", flush=True)

    if not ok:
        raise RuntimeError("A4/V4 etale Prym split audit failed; inspect JSON output.")


if __name__ == "__main__":
    main()

