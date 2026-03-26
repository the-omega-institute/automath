#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit prime-core FRACTRAN compilation of finite partial functions.

This script is English-only by repository convention.

We audit the constructions in:
  - thm:pom-fractran-primecore-finite-partial-function-category
  - cor:pom-fractran-finite-update-table-one-step
  - thm:pom-fractran-permutation-embedding-length
  - thm:pom-fractran-two-prime-denominator-dfa-compile

by exhaustive checks on small deterministic instances.

Outputs:
  - artifacts/export/pom_fractran_primecore_finite_partial_functions_audit.json
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import time
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _fractran_step(N: int, fracs: List[Tuple[int, int]]) -> Optional[int]:
    """One FRACTRAN step: pick first i with N*a_i/b_i integer; else halt (None)."""
    if N < 1:
        raise ValueError("N must be >= 1.")
    for (a, b) in fracs:
        if b <= 0 or a <= 0:
            raise ValueError("FRACTRAN fractions must be positive.")
        if (N * a) % b == 0:
            return (N * a) // b
    return None


def _partial_maps(S: List[int], bot: int) -> Iterable[Dict[int, Optional[int]]]:
    """All partial maps S -> S ∪ {undefined}, encoded by None."""
    choices: List[List[Optional[int]]] = []
    for p in S:
        choices.append([None] + list(S))  # allow undefined and any value in S (including fixed points)
    for vals in itertools.product(*choices):
        yield {p: vals[i] for (i, p) in enumerate(S)}


def _compose_partial(phi: Dict[int, Optional[int]], psi: Dict[int, Optional[int]], S: List[int]) -> Dict[int, Optional[int]]:
    out: Dict[int, Optional[int]] = {}
    for p in S:
        v = phi[p]
        if v is None:
            out[p] = None
        else:
            out[p] = psi[v]
    return out


def _compile_partial_to_fractran(phi: Dict[int, Optional[int]], S: List[int], bot: int) -> List[Tuple[int, int]]:
    """Compile partial map via explicit bot-rules, omit fixed points, append 1/1."""
    fracs: List[Tuple[int, int]] = []
    for p in S:
        v = phi[p]
        if v is None:
            fracs.append((bot, p))
        elif v == p:
            # fixed point: omit denominator p, so it falls through to identity 1/1
            continue
        else:
            fracs.append((v, p))
    fracs.append((1, 1))
    return fracs


def _eval_theta(phi_fracs: List[Tuple[int, int]], S: List[int], bot: int) -> Dict[int, Optional[int]]:
    out: Dict[int, Optional[int]] = {}
    for p in S:
        v = _fractran_step(p, phi_fracs)
        if v is None:
            raise RuntimeError("Program unexpectedly halted (identity should totalize).")
        if v == bot:
            out[p] = None
        else:
            out[p] = v
    return out


def _all_permutations(X: List[int]) -> Iterable[Dict[int, int]]:
    for perm in itertools.permutations(X):
        yield {X[i]: perm[i] for i in range(len(X))}


def _compile_perm_to_fractran(perm: Dict[int, int], S: List[int]) -> List[Tuple[int, int]]:
    fracs: List[Tuple[int, int]] = []
    for p in S:
        q = perm[p]
        if q != p:
            fracs.append((q, p))
    fracs.append((1, 1))
    return fracs


def _compose_perm(a: Dict[int, int], b: Dict[int, int], S: List[int]) -> Dict[int, int]:
    return {p: a[b[p]] for p in S}


def _compile_dfa(Q: List[int], Sigma: List[int], delta: Dict[Tuple[int, int], int]) -> List[Tuple[int, int]]:
    fracs: List[Tuple[int, int]] = []
    for q in Q:
        for s in Sigma:
            fracs.append((delta[(q, s)], q * s))
    return fracs


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit prime-core FRACTRAN finite partial functions.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    t0 = time.time()
    print("[pom-fractran-primecore-finite-partial] start", flush=True)

    # Deterministic test primes.
    S = [2, 3, 5, 7]
    bot = 11
    if bot in S:
        raise RuntimeError("bot must not be in S.")

    # Exhaustive audit: all partial maps on S.
    total_maps = 0
    all_maps_ok = True
    for phi in _partial_maps(S, bot):
        total_maps += 1
        fracs = _compile_partial_to_fractran(phi, S, bot)
        theta = _eval_theta(fracs, S, bot)
        if theta != phi:
            all_maps_ok = False
            break
        # bot should be absorbing (no denominator bot; identity applies)
        vb = _fractran_step(bot, fracs)
        if vb != bot:
            all_maps_ok = False
            break

    # Composition audit on the same finite window: verify sequential execution equals composition.
    # (Full pairwise check is 625^2=390625, still small.)
    comp_ok = True
    phis = list(_partial_maps(S, bot))
    for phi in phis:
        F_phi = _compile_partial_to_fractran(phi, S, bot)
        for psi in phis:
            F_psi = _compile_partial_to_fractran(psi, S, bot)
            comp = _compose_partial(phi, psi, S)  # psi ∘ phi
            F_comp = _compile_partial_to_fractran(comp, S, bot)
            for p in S:
                x1 = _fractran_step(p, F_phi)
                if x1 is None:
                    comp_ok = False
                    break
                x2 = _fractran_step(x1, F_psi)
                if x2 is None:
                    comp_ok = False
                    break
                x3 = _fractran_step(p, F_comp)
                if x3 is None:
                    comp_ok = False
                    break
                if x2 != x3:
                    comp_ok = False
                    break
            if not comp_ok:
                break
        if not comp_ok:
            break

    # Permutation embedding audit on S (as encoded primes).
    # Check homomorphism on all permutations of S.
    perm_ok = True
    perms = list(_all_permutations(S))
    for a in perms:
        Fa = _compile_perm_to_fractran(a, S)
        for b in perms:
            Fb = _compile_perm_to_fractran(b, S)
            ab = _compose_perm(a, b, S)
            Fab = _compile_perm_to_fractran(ab, S)
            for p in S:
                y = _fractran_step(p, Fb)
                if y is None:
                    perm_ok = False
                    break
                z = _fractran_step(y, Fa)
                if z is None:
                    perm_ok = False
                    break
                w = _fractran_step(p, Fab)
                if w is None or z != w:
                    perm_ok = False
                    break
            if not perm_ok:
                break
        if not perm_ok:
            break

    # Two-prime denominator DFA compilation audit (small instance).
    Q = [2, 3, 5]
    Sigma = [7, 11]
    # Ensure disjointness:
    if set(Q) & set(Sigma):
        raise RuntimeError("Q and Sigma primes must be disjoint.")
    delta: Dict[Tuple[int, int], int] = {}
    for q in Q:
        for s in Sigma:
            # deterministic but nontrivial table:
            delta[(q, s)] = Q[(Q.index(q) + Sigma.index(s) + 1) % len(Q)]
    F_dfa = _compile_dfa(Q, Sigma, delta)
    dfa_ok = True
    for q in Q:
        for s in Sigma:
            out = _fractran_step(q * s, F_dfa)
            if out != delta[(q, s)]:
                dfa_ok = False
                break
        if not dfa_ok:
            break

    payload: Dict[str, object] = {
        "S": S,
        "bot": bot,
        "partial_map_count": total_maps,
        "all_partial_maps_ok": bool(all_maps_ok),
        "composition_ok": bool(comp_ok),
        "permutation_homomorphism_ok": bool(perm_ok),
        "dfa_compile_ok": bool(dfa_ok),
        "elapsed_s": float(time.time() - t0),
    }

    if not args.no_output:
        out_json = export_dir() / "pom_fractran_primecore_finite_partial_functions_audit.json"
        _write_json(out_json, payload)

    print("[pom-fractran-primecore-finite-partial] ok", flush=True)


if __name__ == "__main__":
    main()

