#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: S5 splitting field of p7 and three canonical intermediate fields.

This script certifies the group-theoretic arithmetic statements used around:
  - Artin--Dedekind factorizations for K5, K10, K20 (fixed fields of S4, S2xS3, S3),
  - the full Chebotarev splitting-type table for these fields (unramified primes),
  - the quadratic tower K20/K10 and the oriented-flip inertness profile,
  - tame discriminant exponents at the unique odd ramified prime q=985219,
  - character traces at a transposition and the resulting tame conductor exponents.

Outputs:
  - artifacts/export/xi_p7_s5_artin_dedekind_chebotarev_certificate.json
"""

from __future__ import annotations

import argparse
import json
import warnings
from dataclasses import asdict, dataclass
from itertools import permutations
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import sympy as sp
from sympy.utilities.exceptions import SymPyDeprecationWarning

from common_paths import export_dir


def _perm_compose(p: Tuple[int, ...], q: Tuple[int, ...]) -> Tuple[int, ...]:
    """Composition p∘q (apply q then p) on {0,..,4}."""
    return tuple(p[i] for i in q)


def _perm_pow(p: Tuple[int, ...], k: int) -> Tuple[int, ...]:
    r = (0, 1, 2, 3, 4)
    if k < 0:
        raise ValueError("negative powers not needed")
    while k:
        if k & 1:
            r = _perm_compose(p, r)
        p = _perm_compose(p, p)
        k >>= 1
    return r


def _cycle_type_on_points(p: Tuple[int, ...]) -> Tuple[int, ...]:
    """Return cycle lengths partition of 5."""
    seen = [False] * 5
    lens: List[int] = []
    for i in range(5):
        if seen[i]:
            continue
        j = i
        c = 0
        while not seen[j]:
            seen[j] = True
            j = p[j]
            c += 1
        lens.append(c)
    return tuple(sorted(lens, reverse=True))


def _orbit_cycles(p: Tuple[int, ...], space: Sequence[object]) -> List[int]:
    """Cycle lengths of the permutation induced by p on a finite space."""
    idx: Dict[object, int] = {space[i]: i for i in range(len(space))}
    seen = [False] * len(space)
    lens: List[int] = []
    for i in range(len(space)):
        if seen[i]:
            continue
        cur = space[i]
        c = 0
        while True:
            j = idx[cur]
            if seen[j]:
                break
            seen[j] = True
            c += 1
            cur = _act(p, cur)
        lens.append(c)
    lens.sort(reverse=True)
    return lens


def _orbits_count(p: Tuple[int, ...], space: Sequence[object]) -> int:
    """Number of orbits of <p> on space."""
    idx: Dict[object, int] = {space[i]: i for i in range(len(space))}
    seen = [False] * len(space)
    orbits = 0
    for i in range(len(space)):
        if seen[i]:
            continue
        orbits += 1
        cur = space[i]
        while True:
            j = idx[cur]
            if seen[j]:
                break
            seen[j] = True
            cur = _act(p, cur)
    return orbits


def _format_partition_lens(lens: Iterable[int]) -> str:
    """Format multiset of cycle lengths as '6^2·3^2·2' etc."""
    counts: Dict[int, int] = {}
    for L in lens:
        counts[L] = counts.get(L, 0) + 1
    parts = []
    for L in sorted(counts.keys(), reverse=True):
        e = counts[L]
        if e == 1:
            parts.append(f"{L}")
        else:
            parts.append(f"{L}^{e}")
    return r"\cdot ".join(parts) if parts else "1"


def _act(p: Tuple[int, ...], obj: object) -> object:
    if isinstance(obj, int):
        return p[obj]
    if isinstance(obj, tuple) and len(obj) == 2:
        a, b = obj
        if isinstance(a, int) and isinstance(b, int):
            # ordered pair
            return (p[a], p[b])
    if isinstance(obj, tuple) and len(obj) == 2 and all(isinstance(z, int) for z in obj):
        return (p[obj[0]], p[obj[1]])
    if isinstance(obj, frozenset):
        return frozenset(p[i] for i in obj)
    raise TypeError(f"unsupported action object: {obj!r}")


def _space_points() -> List[int]:
    return list(range(5))


def _space_2subsets() -> List[frozenset[int]]:
    pts = range(5)
    subs: List[frozenset[int]] = []
    for i in pts:
        for j in pts:
            if i < j:
                subs.append(frozenset({i, j}))
    return subs


def _space_ordered_pairs() -> List[Tuple[int, int]]:
    pairs: List[Tuple[int, int]] = []
    for i in range(5):
        for j in range(5):
            if i != j:
                pairs.append((i, j))
    return pairs


def _fixed_points_count(p: Tuple[int, ...], space: Sequence[object]) -> int:
    return sum(1 for x in space if _act(p, x) == x)


def _conjugacy_classes_S5() -> Dict[Tuple[int, ...], List[Tuple[int, ...]]]:
    """Group all 120 permutations by point-cycle-type partition."""
    classes: Dict[Tuple[int, ...], List[Tuple[int, ...]]] = {}
    for perm in permutations(range(5)):
        p = tuple(int(x) for x in perm)
        ct = _cycle_type_on_points(p)
        classes.setdefault(ct, []).append(p)
    return classes


def _rep_for_cycle_type(ct: Tuple[int, ...]) -> Tuple[int, ...]:
    """Pick a representative permutation with cycle type ct."""
    classes = _conjugacy_classes_S5()
    if ct not in classes:
        raise KeyError(f"cycle type {ct} not present")
    return classes[ct][0]


def _inert_primes_profile_in_K20_over_K10(sigma: Tuple[int, ...]) -> List[Tuple[int, int]]:
    """Return list of (m, count) for inert primes of residue degree m in K10."""
    subs = _space_2subsets()
    # Partition into sigma-orbits.
    idx: Dict[frozenset[int], int] = {subs[i]: i for i in range(len(subs))}
    seen = [False] * len(subs)
    inert_degrees: List[int] = []
    for i in range(len(subs)):
        if seen[i]:
            continue
        start = subs[i]
        orb: List[frozenset[int]] = []
        cur = start
        while True:
            j = idx[cur]
            if seen[j]:
                break
            seen[j] = True
            orb.append(cur)
            cur = _act(sigma, cur)  # type: ignore[arg-type]
        m = len(orb)
        # decide inertness: sigma^m swaps endpoints on the (unordered) edge
        a, b = sorted(list(start))
        sm = _perm_pow(sigma, m)
        swapped = (sm[a] == b) and (sm[b] == a)
        if swapped:
            inert_degrees.append(m)
    # compress
    counts: Dict[int, int] = {}
    for m in inert_degrees:
        counts[m] = counts.get(m, 0) + 1
    return sorted(((m, c) for m, c in counts.items()), key=lambda t: t[0])


@dataclass(frozen=True)
class TableRow:
    cycle_type: str
    class_size: int
    density: str
    K5: str
    K10: str
    K20: str
    inert_in_K20_over_K10: str


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit p7 S5 intermediate fields: zeta/Artin and Chebotarev profiles.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "xi_p7_s5_artin_dedekind_chebotarev_certificate.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)

    # Polynomial and discriminant check for q.
    x = sp.Symbol("x")
    p7 = sp.Poly(x**5 - 2 * x**4 - 7 * x**3 - 2 * x + 2, x, domain=sp.ZZ)
    disc_p7 = int(sp.discriminant(p7.as_expr(), x))
    q = 985219
    disc_factor = sp.factorint(abs(disc_p7))
    sf = (-1 if disc_p7 < 0 else 1)
    for p, e in disc_factor.items():
        if e % 2 == 1:
            sf *= int(p)
    sf = int(sf)

    # Factor p7 mod q (degree 5, quick) to certify "split with one double root".
    p7_mod_q = sp.Poly(p7.as_expr(), x, domain=sp.GF(q))
    f_mod_q = sp.factor_list(p7_mod_q)[1]
    mod_q_factor_degrees_mults = sorted([(int(f.degree()), int(m)) for (f, m) in f_mod_q])

    points = _space_points()
    subs = _space_2subsets()
    pairs = _space_ordered_pairs()

    classes = _conjugacy_classes_S5()
    # Canonical order of cycle types (as used in the paper statement).
    ordered_cycle_types: List[Tuple[int, ...]] = [
        (1, 1, 1, 1, 1),
        (2, 1, 1, 1),
        (2, 2, 1),
        (3, 1, 1),
        (3, 2),
        (4, 1),
        (5,),
    ]

    rows: List[TableRow] = []
    for ct in ordered_cycle_types:
        elems = classes[ct]
        rep = elems[0]
        size = len(elems)
        dens = f"{size}/120"
        K5_lens = _orbit_cycles(rep, points)
        K10_lens = _orbit_cycles(rep, subs)
        K20_lens = _orbit_cycles(rep, pairs)
        inert_profile = _inert_primes_profile_in_K20_over_K10(rep)
        inert_str = ", ".join([f"{c}×f={m}" for (m, c) in inert_profile]) if inert_profile else "none"

        def _ct_str(ct_: Tuple[int, ...]) -> str:
            # (2,1,1,1) -> 2·1^3 etc
            counts: Dict[int, int] = {}
            for L in ct_:
                counts[L] = counts.get(L, 0) + 1
            parts = []
            for L in sorted(counts.keys(), reverse=True):
                e = counts[L]
                if e == 1:
                    parts.append(f"{L}")
                else:
                    parts.append(f"{L}^{e}")
            return r"\cdot ".join(parts)

        rows.append(
            TableRow(
                cycle_type=_ct_str(ct),
                class_size=size,
                density=dens,
                K5=_format_partition_lens(K5_lens),
                K10=_format_partition_lens(K10_lens),
                K20=_format_partition_lens(K20_lens),
                inert_in_K20_over_K10=inert_str,
            )
        )

    # Tame discriminant exponents via orbit counts of a transposition.
    tau = _rep_for_cycle_type((2, 1, 1, 1))  # any transposition
    orbits_points = _orbits_count(tau, points)
    orbits_subs = _orbits_count(tau, subs)
    orbits_pairs = _orbits_count(tau, pairs)
    disc_exp_K5 = len(points) - orbits_points
    disc_exp_K10 = len(subs) - orbits_subs
    disc_exp_K20 = len(pairs) - orbits_pairs

    # Character traces at tau from permutation actions.
    chi_points = _fixed_points_count(tau, points)  # Ind_{S4} 1
    chi_subs = _fixed_points_count(tau, subs)  # Ind_{S2xS3} 1
    chi_pairs = _fixed_points_count(tau, pairs)  # Ind_{S3} 1

    # Specht characters at a transposition extracted from the decompositions.
    # Ind_{S4} 1 = 1 + rho4, dim(rho4)=4.
    chi_rho4 = chi_points - 1
    # Ind_{S2xS3} 1 = 1 + rho4 + rho5, dim(rho5)=5.
    chi_rho5 = chi_subs - 1 - chi_rho4
    # Ind_{S3} 1 = 1 + 2 rho4 + rho5 + rho6, dim(rho6)=6.
    chi_rho6 = chi_pairs - 1 - 2 * chi_rho4 - chi_rho5

    dims = {"rho4": 4, "rho5": 5, "rho6": 6}
    chis = {"rho4": chi_rho4, "rho5": chi_rho5, "rho6": chi_rho6}
    inv_dims = {k: (dims[k] + chis[k]) // 2 for k in dims}
    conductors = {k: (dims[k] - chis[k]) // 2 for k in dims}

    payload: Dict[str, object] = {
        "meta": {"script": Path(__file__).name, "sympy": sp.__version__},
        "p7": {
            "poly": str(p7.as_expr()),
            "disc": disc_p7,
            "disc_factorint_abs": {str(k): int(v) for k, v in disc_factor.items()},
            "squarefree_part_with_sign": sf,
            "q": q,
            "disc_matches_minus_16q": (disc_p7 == -16 * q),
            "squarefree_part_matches_minus_q": (sf == -q),
            "factor_mod_q_degree_mults": mod_q_factor_degrees_mults,
        },
        "S5": {
            "order": 120,
            "conjugacy_classes_by_cycle_type": {",".join(map(str, k)): len(v) for k, v in classes.items()},
        },
        "chebotarev_splitting_table": [asdict(r) for r in rows],
        "tame_orbit_counts_at_transposition": {
            "tau_cycle_type": r"\cdot ".join(["2", "1^3"]),
            "points_orbits": orbits_points,
            "two_subsets_orbits": orbits_subs,
            "ordered_pairs_orbits": orbits_pairs,
        },
        "tame_discriminant_exponents_at_q": {
            "v_q_Disc_K5": disc_exp_K5,
            "v_q_Disc_K10": disc_exp_K10,
            "v_q_Disc_K20": disc_exp_K20,
        },
        "transposition_character_traces": {
            "chi_Ind_S4": chi_points,
            "chi_Ind_S2xS3": chi_subs,
            "chi_Ind_S3": chi_pairs,
            "chi_rho4": chi_rho4,
            "chi_rho5": chi_rho5,
            "chi_rho6": chi_rho6,
        },
        "tame_invariant_dimensions_at_q": inv_dims,
        "tame_conductor_exponents_at_q": conductors,
    }

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[xi-p7-s5-artin-dedekind-chebotarev] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

