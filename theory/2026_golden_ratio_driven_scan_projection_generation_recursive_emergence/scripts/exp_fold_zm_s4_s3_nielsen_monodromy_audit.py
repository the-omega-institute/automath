#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit certificates for Nielsen-class and braid-monodromy statements in passport (4)(2)^5:

  - |Ni^in(S4; C4, C2^5)| = 160 (with one distinguished C4 slot),
  - braid B5 transitivity on the 160 inner classes,
  - quotient projection S4 -> S4/V4 ~= S3 induces
      |Ni^in(S3; T^6)| = 40
    and a uniform 4-to-1 block system (160 -> 40),
  - block-action monodromy order 25920 with rank-3 subdegrees (1,12,27),
    center trivial and derived subgroup full (perfect),
  - 40-point generator cycle type 3^9 1^13,
    160-point generator cycle type 3^36 2^12 1^28,
  - 160-point braid image order and kernel size in the block projection.

Outputs:
  - artifacts/export/fold_zm_s4_s3_nielsen_monodromy_audit.json
"""

from __future__ import annotations

import json
import os
import time
from collections import Counter, defaultdict, deque
from itertools import permutations, product
from pathlib import Path
from typing import DefaultDict, Dict, Iterable, List, Sequence, Tuple

from sympy.combinatorics.perm_groups import PermutationGroup
from sympy.combinatorics.permutations import Permutation as SymPermutation

from common_paths import export_dir


Perm = Tuple[int, ...]
Tuple6 = Tuple[Perm, Perm, Perm, Perm, Perm, Perm]


def _id_perm(n: int) -> Perm:
    return tuple(range(n))


def _compose(p: Perm, q: Perm) -> Perm:
    # Composition p ∘ q.
    return tuple(p[q[i]] for i in range(len(p)))


def _inv(p: Perm) -> Perm:
    n = len(p)
    out = [0] * n
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)


def _conj(h: Perm, g: Perm) -> Perm:
    return _compose(_compose(h, g), _inv(h))


def _tuple_conj(h: Perm, t: Tuple6) -> Tuple6:
    return tuple(_conj(h, x) for x in t)  # type: ignore[return-value]


def _cycle_type(p: Perm) -> Tuple[int, ...]:
    n = len(p)
    seen = [False] * n
    out: List[int] = []
    for i in range(n):
        if seen[i]:
            continue
        j = i
        cyc_len = 0
        while not seen[j]:
            seen[j] = True
            cyc_len += 1
            j = p[j]
        if cyc_len > 1:
            out.append(cyc_len)
    out.sort(reverse=True)
    return tuple(out)


def _cycle_multiset(p: Perm) -> Dict[int, int]:
    n = len(p)
    seen = [False] * n
    cnt: Counter[int] = Counter()
    for i in range(n):
        if seen[i]:
            continue
        j = i
        cyc_len = 0
        while not seen[j]:
            seen[j] = True
            cyc_len += 1
            j = p[j]
        cnt[cyc_len] += 1
    return dict(sorted(cnt.items()))


def _subgroup_generated(gens: Sequence[Perm], n: int) -> set[Perm]:
    e = _id_perm(n)
    seen: set[Perm] = {e}
    q: deque[Perm] = deque([e])
    while q:
        a = q.popleft()
        for g in gens:
            b = _compose(a, g)
            if b not in seen:
                seen.add(b)
                q.append(b)
    return seen


def _hurwitz_sigma(t: Tuple6, i: int) -> Tuple6:
    # i in {0,1,2,3}, acts on finite slots g1..g5.
    g0, g1, g2, g3, g4, g5 = t
    gs = [g1, g2, g3, g4, g5]
    a = gs[i]
    b = gs[i + 1]
    gs[i] = b
    gs[i + 1] = _compose(_compose(_inv(b), a), b)
    return (g0, gs[0], gs[1], gs[2], gs[3], gs[4])


def _hurwitz_sigma_inv(t: Tuple6, i: int) -> Tuple6:
    g0, g1, g2, g3, g4, g5 = t
    gs = [g1, g2, g3, g4, g5]
    a = gs[i]
    b = gs[i + 1]
    gs[i] = _compose(_compose(a, b), _inv(a))
    gs[i + 1] = a
    return (g0, gs[0], gs[1], gs[2], gs[3], gs[4])


def _canonicalize_inner(raw_tuples: Sequence[Tuple6], group_elements: Sequence[Perm]) -> Tuple[List[Tuple6], Dict[Tuple6, int]]:
    rep_to_id: Dict[Tuple6, int] = {}
    tuple_to_id: Dict[Tuple6, int] = {}
    reps: List[Tuple6] = []
    for t in raw_tuples:
        rep = min(_tuple_conj(h, t) for h in group_elements)
        cid = rep_to_id.get(rep)
        if cid is None:
            cid = len(reps)
            rep_to_id[rep] = cid
            reps.append(rep)
        tuple_to_id[t] = cid
    return reps, tuple_to_id


def _enumerate_s4_raw() -> Tuple[List[Tuple6], List[Perm], List[Perm], List[Perm]]:
    S4: List[Perm] = [tuple(p) for p in permutations(range(4))]
    C4 = [g for g in S4 if _cycle_type(g) == (4,)]
    C2 = [g for g in S4 if _cycle_type(g) == (2,)]
    full = set(S4)

    out: List[Tuple6] = []
    for g0 in C4:
        for g1, g2, g3, g4 in product(C2, repeat=4):
            prefix = _compose(_compose(_compose(_compose(g0, g1), g2), g3), g4)
            g5 = _inv(prefix)  # enforce g0 g1 g2 g3 g4 g5 = 1
            if g5 not in C2:
                continue
            t = (g0, g1, g2, g3, g4, g5)
            if _subgroup_generated(t, 4) != full:
                continue
            out.append(t)
    return out, S4, C4, C2


def _enumerate_s3_raw() -> Tuple[List[Tuple6], List[Perm], List[Perm]]:
    S3: List[Perm] = [tuple(p) for p in permutations(range(3))]
    T = [g for g in S3 if _cycle_type(g) == (2,)]
    full = set(S3)

    out: List[Tuple6] = []
    for h0 in T:
        for h1, h2, h3, h4 in product(T, repeat=4):
            prefix = _compose(_compose(_compose(_compose(h0, h1), h2), h3), h4)
            h5 = _inv(prefix)
            if h5 not in T:
                continue
            t = (h0, h1, h2, h3, h4, h5)
            if _subgroup_generated(t, 3) != full:
                continue
            out.append(t)
    return out, S3, T


def _perm_action_from_generators(
    reps: Sequence[Tuple6],
    tuple_to_class: Dict[Tuple6, int],
    group_elements: Sequence[Perm],
) -> Tuple[List[Perm], List[Perm]]:
    # Returns generator permutations for sigma_i and sigma_i^{-1}, i=1..4.
    sigma: List[Perm] = []
    sigma_inv: List[Perm] = []
    n = len(reps)
    for i in range(4):
        img = [0] * n
        img_inv = [0] * n
        for cid, rep in enumerate(reps):
            nxt = _hurwitz_sigma(rep, i)
            nxt_rep = min(_tuple_conj(h, nxt) for h in group_elements)
            img[cid] = tuple_to_class[nxt_rep]

            nxt2 = _hurwitz_sigma_inv(rep, i)
            nxt2_rep = min(_tuple_conj(h, nxt2) for h in group_elements)
            img_inv[cid] = tuple_to_class[nxt2_rep]
        sigma.append(tuple(img))
        sigma_inv.append(tuple(img_inv))
    return sigma, sigma_inv


def _orbit_size(generators: Sequence[Perm], start: int) -> int:
    seen = {start}
    q = deque([start])
    while q:
        x = q.popleft()
        for g in generators:
            y = g[x]
            if y not in seen:
                seen.add(y)
                q.append(y)
    return len(seen)


def _project_s4_to_s3_map(S4: Sequence[Perm]) -> Dict[Perm, Perm]:
    # Via conjugation action on the three nontrivial elements of V4.
    d0 = (1, 0, 3, 2)  # (12)(34)
    d1 = (2, 3, 0, 1)  # (13)(24)
    d2 = (3, 2, 1, 0)  # (14)(23)
    basis = [d0, d1, d2]
    idx = {d0: 0, d1: 1, d2: 2}
    out: Dict[Perm, Perm] = {}
    for g in S4:
        perm = []
        g_inv = _inv(g)
        for d in basis:
            c = _compose(_compose(g, d), g_inv)
            perm.append(idx[c])
        out[g] = tuple(perm)
    return out


def _group_from_generators(gens: Sequence[Perm], n: int) -> set[Perm]:
    e = _id_perm(n)
    inv_gens = [_inv(g) for g in gens]
    all_gens = list(gens) + inv_gens
    seen: set[Perm] = {e}
    q: deque[Perm] = deque([e])
    while q:
        a = q.popleft()
        for g in all_gens:
            b = _compose(a, g)
            if b not in seen:
                seen.add(b)
                q.append(b)
    return seen


def _stabilizer_subdegrees(group: Sequence[Perm], point: int, n: int) -> List[int]:
    stab = [g for g in group if g[point] == point]
    unseen = set(range(n))
    out: List[int] = []
    while unseen:
        seed = next(iter(unseen))
        orb = {seed}
        q = deque([seed])
        while q:
            x = q.popleft()
            for g in stab:
                y = g[x]
                if y not in orb:
                    orb.add(y)
                    q.append(y)
        unseen -= orb
        out.append(len(orb))
    out.sort()
    return out


def _center_size_via_generators(group: Sequence[Perm], generators: Sequence[Perm]) -> int:
    z = 0
    for a in group:
        if all(_compose(a, g) == _compose(g, a) for g in generators):
            z += 1
    return z


def _derived_subgroup_order(group: Sequence[Perm], generators: Sequence[Perm], n: int) -> int:
    comms: List[Perm] = []
    for a in group:
        a_inv = _inv(a)
        for b in generators:
            b_inv = _inv(b)
            c = _compose(_compose(_compose(a_inv, b_inv), a), b)
            comms.append(c)
    dsub = _group_from_generators(comms, n)
    return len(dsub)


def _sympy_group_order(gens: Sequence[Perm]) -> int:
    pg = PermutationGroup([SymPermutation(list(g)) for g in gens])
    return int(pg.order())


def main() -> None:
    t0 = time.time()
    print("[fold-zm-s4-s3-nielsen-monodromy-audit] start", flush=True)

    # ---------- S4 inner Nielsen class (4)(2)^5 ----------
    raw_s4, S4, C4, C2 = _enumerate_s4_raw()
    print("[fold-zm-s4-s3-nielsen-monodromy-audit] enumerated raw S4 tuples", flush=True)
    reps_s4, tuple_to_class_s4 = _canonicalize_inner(raw_s4, S4)
    n_s4 = len(reps_s4)
    raw_s4_count = len(raw_s4)

    if raw_s4_count != 3840:
        raise RuntimeError(f"Unexpected raw S4 tuple count: {raw_s4_count} (expected 3840).")
    if n_s4 != 160:
        raise RuntimeError(f"Unexpected S4 inner Nielsen count: {n_s4} (expected 160).")

    sigma_s4, sigma_s4_inv = _perm_action_from_generators(reps_s4, tuple_to_class_s4, S4)
    print("[fold-zm-s4-s3-nielsen-monodromy-audit] built S4 braid action on inner classes", flush=True)
    orbit_s4 = _orbit_size(sigma_s4 + sigma_s4_inv, 0)
    if orbit_s4 != n_s4:
        raise RuntimeError(f"S4 B5 orbit is not transitive: orbit={orbit_s4}, total={n_s4}.")

    # ---------- Quotient map S4 -> S3 ----------
    pi_map = _project_s4_to_s3_map(S4)
    image_pi = {pi_map[g] for g in S4}
    if len(image_pi) != 6:
        raise RuntimeError(f"Projection image size is {len(image_pi)}; expected 6.")

    # ---------- S3 inner Nielsen class T^6 ----------
    raw_s3, S3, T3 = _enumerate_s3_raw()
    print("[fold-zm-s4-s3-nielsen-monodromy-audit] enumerated raw S3 tuples", flush=True)
    reps_s3, tuple_to_class_s3 = _canonicalize_inner(raw_s3, S3)
    n_s3 = len(reps_s3)
    raw_s3_count = len(raw_s3)

    if raw_s3_count != 240:
        raise RuntimeError(f"Unexpected raw S3 tuple count: {raw_s3_count} (expected 240).")
    if n_s3 != 40:
        raise RuntimeError(f"Unexpected S3 inner Nielsen count: {n_s3} (expected 40).")

    sigma_s3, sigma_s3_inv = _perm_action_from_generators(reps_s3, tuple_to_class_s3, S3)
    print("[fold-zm-s4-s3-nielsen-monodromy-audit] built S3 braid action on inner classes", flush=True)
    orbit_s3 = _orbit_size(sigma_s3 + sigma_s3_inv, 0)
    if orbit_s3 != n_s3:
        raise RuntimeError(f"S3 B5 orbit is not transitive: orbit={orbit_s3}, total={n_s3}.")

    # ---------- Fiber partition S4 classes -> S3 classes ----------
    class_to_s3: Dict[int, int] = {}
    fibers: DefaultDict[int, List[int]] = defaultdict(list)
    for cid, rep in enumerate(reps_s4):
        proj = tuple(pi_map[g] for g in rep)  # type: ignore[arg-type]
        proj_rep = min(_tuple_conj(h, proj) for h in S3)
        sid = tuple_to_class_s3[proj_rep]
        class_to_s3[cid] = sid
        fibers[sid].append(cid)

    if len(fibers) != n_s3:
        raise RuntimeError(f"Projection not surjective onto S3 classes: got {len(fibers)} blocks, expected {n_s3}.")
    block_sizes = sorted(len(v) for v in fibers.values())
    if block_sizes != [4] * n_s3:
        raise RuntimeError(f"Fiber sizes are not uniformly 4: {Counter(block_sizes)}")

    # ---------- Check induced block action matches S3 action ----------
    induced_block_gens: List[Perm] = []
    for g160 in sigma_s4:
        img = [0] * n_s3
        for sid, members in fibers.items():
            target_sid = class_to_s3[g160[members[0]]]
            if any(class_to_s3[g160[m]] != target_sid for m in members):
                raise RuntimeError("A braid generator does not preserve block fibers.")
            img[sid] = target_sid
        induced_block_gens.append(tuple(img))
    if induced_block_gens != sigma_s3:
        raise RuntimeError("Induced block action does not match direct S3 Nielsen action.")
    print("[fold-zm-s4-s3-nielsen-monodromy-audit] validated 4-block projection", flush=True)

    # ---------- 40-point monodromy invariants ----------
    gens40 = sigma_s3
    G40 = PermutationGroup([SymPermutation(list(g)) for g in gens40])
    order40 = int(G40.order())
    if order40 != 25920:
        raise RuntimeError(f"Unexpected |Gamma_S3|={order40}, expected 25920.")

    subdegrees = sorted(len(orb) for orb in G40.stabilizer(0).orbits())
    if subdegrees != [1, 12, 27]:
        raise RuntimeError(f"Unexpected subdegrees: {subdegrees}, expected [1, 12, 27].")

    center40 = int(G40.center().order())
    derived40 = int(G40.derived_subgroup().order())
    if center40 != 1:
        raise RuntimeError(f"Unexpected center size for Gamma_S3: {center40}, expected 1.")
    if derived40 != order40:
        raise RuntimeError(f"Unexpected derived subgroup order: {derived40}, expected {order40}.")

    sigma40_cycle_types = [_cycle_multiset(g) for g in gens40]

    # ---------- 160-point monodromy order, kernel, cycle types ----------
    gens160 = sigma_s4
    claimed_order160 = 2**102 * 3**44 * 5
    compute_order160 = os.environ.get("XI_COMPUTE_GAMMA_S4_ORDER", "0") == "1"
    order160 = claimed_order160
    if compute_order160:
        print("[fold-zm-s4-s3-nielsen-monodromy-audit] computing |Gamma_S4| via Schreier-Sims", flush=True)
        order160 = _sympy_group_order(gens160)
    order40_sympy = _sympy_group_order(gens40)
    if order40_sympy != order40:
        raise RuntimeError(f"Sympy/group-closure order mismatch on 40-point action: {order40_sympy} vs {order40}.")
    if compute_order160 and order160 != claimed_order160:
        raise RuntimeError(f"|Gamma_S4| mismatch: computed {order160}, claimed {claimed_order160}.")
    if order160 % order40 != 0:
        raise RuntimeError(f"|Gamma_S4| not divisible by |Gamma_S3|: {order160} mod {order40}.")
    kernel_order = order160 // order40

    sigma160_cycle_types = [_cycle_multiset(g) for g in gens160]

    expected_160 = {1: 28, 2: 12, 3: 36}
    expected_40 = {1: 13, 3: 9}
    if any(ct != expected_160 for ct in sigma160_cycle_types):
        raise RuntimeError(f"Unexpected 160-point generator cycle types: {sigma160_cycle_types}")
    if any(ct != expected_40 for ct in sigma40_cycle_types):
        raise RuntimeError(f"Unexpected 40-point generator cycle types: {sigma40_cycle_types}")

    payload: Dict[str, object] = {
        "meta": {
            "script": Path(__file__).name,
            "generated_at_unix_s": time.time(),
            "seconds": float(time.time() - t0),
        },
        "passport": "(4)(2)^5 with distinguished C4 branch point",
        "s4_inner_nielsen": {
            "raw_tuple_count": int(raw_s4_count),
            "inner_class_count": int(n_s4),
            "num_4cycles": int(len(C4)),
            "num_transpositions": int(len(C2)),
            "b5_transitive": bool(orbit_s4 == n_s4),
        },
        "s3_inner_nielsen": {
            "raw_tuple_count": int(raw_s3_count),
            "inner_class_count": int(n_s3),
            "num_transpositions": int(len(T3)),
            "b5_transitive": bool(orbit_s3 == n_s3),
        },
        "projection_s4_to_s3": {
            "image_size": int(len(image_pi)),
            "fiber_count": int(len(fibers)),
            "fiber_size_multiset": dict(sorted(Counter(block_sizes).items())),
            "fiber_uniform_size": int(block_sizes[0]),
        },
        "gamma_s3_on_40": {
            "order": int(order40),
            "center_size": int(center40),
            "derived_subgroup_order": int(derived40),
            "is_perfect": bool(derived40 == order40),
            "subdegrees_at_point_0": [int(x) for x in subdegrees],
            "sigma_cycle_types": sigma40_cycle_types,
        },
        "gamma_s4_on_160": {
            "order": int(order160),
            "order_claimed_formula": "2^102 * 3^44 * 5",
            "order160_verified_in_run": bool(compute_order160),
            "sigma_cycle_types": sigma160_cycle_types,
            "block_kernel_order": int(kernel_order),
            "block_quotient_order": int(order40),
        },
        "expected_values_check": {
            "nielsen_s4_inner_160": bool(n_s4 == 160),
            "nielsen_s3_inner_40": bool(n_s3 == 40),
            "fiber_size_4": bool(block_sizes == [4] * n_s3),
            "gamma_s3_order_25920": bool(order40 == 25920),
            "gamma_s3_subdegrees_1_12_27": bool(subdegrees == [1, 12, 27]),
            "sigma160_type_3^36_2^12_1^28": bool(all(ct == expected_160 for ct in sigma160_cycle_types)),
            "sigma40_type_3^9_1^13": bool(all(ct == expected_40 for ct in sigma40_cycle_types)),
        },
    }

    out_json = export_dir() / "fold_zm_s4_s3_nielsen_monodromy_audit.json"
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[fold-zm-s4-s3-nielsen-monodromy-audit] wrote {out_json}", flush=True)


if __name__ == "__main__":
    main()

