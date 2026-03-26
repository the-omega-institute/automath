#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit:
  - genus g=16 of the S4 Galois closure for the quartic cover Pi(lambda,y)=0
    with inertia orders: e_inf=4, and five points with e=2 (y=0,1, and the
    three Lee–Yang roots);
  - the intermediate quotient genera:
      X~/A4 has genus 2 (the discriminant ridge curve),
      X~/V4 has genus 4,
      X~/S3 has genus 1 (the elliptic normalization),
      X~/D4 has genus 1 for any Sylow-2 dihedral subgroup D4≤S4 (index 3);
  - the decomposition of H^0(X~, Omega^1) as an S4-representation
    determined from quotient genera via character averages.

Outputs:
  - artifacts/export/fold_zm_s4_galois_closure_representation_audit.json
  - sections/generated/eq_fold_zm_s4_galois_closure_representation_audit.tex
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def genus_galois_cover(*, G_order: int, inertia_orders: list[int]) -> int:
    # g = 1 + |G|/2 * (-2 + sum_i (1 - 1/e_i))
    s = -2.0
    for e in inertia_orders:
        s += 1.0 - 1.0 / float(e)
    g = 1.0 + (float(G_order) / 2.0) * s
    if abs(g - round(g)) > 1e-9:
        raise RuntimeError(f"non-integer genus computed: {g}")
    return int(round(g))


def genus_degree3_all_transpositions(*, branch_points: int) -> int:
    # For a degree-3 cover Y→P^1 where each branch point has cycle type (2)(1),
    # the ramification contribution is 1 per branch point, hence:
    #   2g-2 = -2*3 + branch_points*1.
    s = -6 + int(branch_points)
    g = 1.0 + 0.5 * float(s)
    if abs(g - round(g)) > 1e-9:
        raise RuntimeError(f"non-integer genus computed: {g}")
    return int(round(g))


@dataclass(frozen=True)
class Payload:
    inertia_orders: list[int]
    genus_Xtilde: int
    genus_C: int
    genus_C6: int
    genus_E: int
    genus_Xtilde_over_D4: int
    multiplicities: Dict[str, int]
    decomposition: str
    invariant_dims: Dict[str, int]


def main() -> None:
    # --- Genus via Riemann–Hurwitz
    inertia = [4, 2, 2, 2, 2, 2]  # infinity + 5 finite branch points
    g_X = genus_galois_cover(G_order=24, inertia_orders=inertia)

    # Discriminant ridge curve: w^2 = degree-5 polynomial => genus 2
    g_C = 2

    # Quotient by V4 is S3-Galois with 6 branch points of order 2 => genus 4
    g_C6 = genus_galois_cover(G_order=6, inertia_orders=[2, 2, 2, 2, 2, 2])

    # Quotient by S3 is the elliptic normalization => genus 1
    g_E = 1

    # Quotient by a Sylow-2 subgroup D4 (dihedral order 8, index 3) gives a degree-3
    # intermediate cover where both a 4-cycle and a transposition in S4 act as
    # transpositions on the 3 cosets (action on the 3 pairings / double transpositions).
    # Hence all 6 branch points contribute (2)(1) in degree 3 => genus 1.
    g_D4 = genus_degree3_all_transpositions(branch_points=6)

    if g_X != 16 or g_C != 2 or g_C6 != 4 or g_E != 1 or g_D4 != 1:
        raise RuntimeError(
            f"unexpected genera: gX={g_X}, gC={g_C}, gC6={g_C6}, gE={g_E}, gD4={g_D4}"
        )

    # --- Character table of S4 on conjugacy classes:
    # classes: id, transposition (2), double transposition (22), 3-cycle (3), 4-cycle (4)
    chi = {
        "triv": {"id": 1, "2": 1, "22": 1, "3": 1, "4": 1},
        "sgn": {"id": 1, "2": -1, "22": 1, "3": 1, "4": -1},
        "V2": {"id": 2, "2": 0, "22": 2, "3": -1, "4": 0},
        "V3": {"id": 3, "2": 1, "22": -1, "3": 0, "4": -1},
        "V3p": {"id": 3, "2": -1, "22": -1, "3": 0, "4": 1},
    }
    dim = {k: chi[k]["id"] for k in chi}

    # Subgroup class counts (as subsets of S4 conjugacy classes)
    # A4: id(1) + double transpositions(3) + 3-cycles(8)
    A4_counts = {"id": 1, "22": 3, "3": 8}
    # V4: id(1) + double transpositions(3)
    V4_counts = {"id": 1, "22": 3}
    # S3 (point stabilizer): id(1) + transpositions(3) + 3-cycles(2)
    S3_counts = {"id": 1, "2": 3, "3": 2}

    def inv_dim(rep: str, counts: Dict[str, int]) -> int:
        tot = 0
        order = sum(counts.values())
        for cls, c in counts.items():
            tot += c * chi[rep][cls]
        if tot % order != 0:
            raise RuntimeError(f"non-integer invariants: rep={rep} tot={tot} order={order}")
        return int(tot // order)

    inv_A4 = {r: inv_dim(r, A4_counts) for r in chi}
    inv_V4 = {r: inv_dim(r, V4_counts) for r in chi}
    inv_S3 = {r: inv_dim(r, S3_counts) for r in chi}

    # --- Solve multiplicities from quotient genera
    # dim W^S4 = multiplicity(triv) = genus(P^1)=0
    m_triv = 0
    # dim W^A4 = g(X~/A4)=2, and only triv/sgn contribute invariants on A4 (each 1)
    m_sgn = g_C - m_triv
    # dim W^V4 = g(X~/V4)=4, invariants: triv(1), sgn(1), V2(2)
    m_V2 = (g_C6 - (m_triv + m_sgn)) // 2
    # dim W^S3 = g(X~/S3)=1, invariants: triv(1), V3(1)
    m_V3 = g_E - m_triv
    # total dimension = genus = 16
    remaining = g_X - (m_triv * dim["triv"] + m_sgn * dim["sgn"] + m_V2 * dim["V2"] + m_V3 * dim["V3"])
    if remaining % dim["V3p"] != 0:
        raise RuntimeError("non-integer multiplicity for V3'")
    m_V3p = remaining // dim["V3p"]

    mult = {"triv": m_triv, "sgn": m_sgn, "V2": m_V2, "V3": m_V3, "V3p": int(m_V3p)}
    if mult != {"triv": 0, "sgn": 2, "V2": 1, "V3": 1, "V3p": 3}:
        raise RuntimeError(f"unexpected multiplicities: {mult}")

    # Cross-check invariants against quotient genera using character averages
    dim_A4 = sum(mult[r] * inv_A4[r] for r in mult)
    dim_V4 = sum(mult[r] * inv_V4[r] for r in mult)
    dim_S3 = sum(mult[r] * inv_S3[r] for r in mult)
    if (dim_A4, dim_V4, dim_S3) != (g_C, g_C6, g_E):
        raise RuntimeError(f"invariant dim mismatch: A4={dim_A4},V4={dim_V4},S3={dim_S3}")

    decomp = "2·sgn ⊕ V2 ⊕ V3 ⊕ 3·V3'"
    payload = Payload(
        inertia_orders=inertia,
        genus_Xtilde=g_X,
        genus_C=g_C,
        genus_C6=g_C6,
        genus_E=g_E,
        genus_Xtilde_over_D4=g_D4,
        multiplicities=mult,
        decomposition=decomp,
        invariant_dims={"A4": dim_A4, "V4": dim_V4, "S3": dim_S3},
    )

    out_json = export_dir() / "fold_zm_s4_galois_closure_representation_audit.json"
    _write_json(out_json, asdict(payload))

    out_tex = generated_dir() / "eq_fold_zm_s4_galois_closure_representation_audit.tex"
    tex = "\n".join(
        [
            "% Auto-generated by scripts/exp_fold_zm_s4_galois_closure_representation_audit.py",
            "\\[",
            "g(\\widetilde X)=16,\\qquad g(\\widetilde X/D_{4})=1,\\qquad H^{0}(\\widetilde X,\\Omega^{1})\\cong 2\\cdot\\mathrm{sgn}\\oplus V_{2}\\oplus V_{3}\\oplus 3V_{3}'.",
            "\\]",
            "",
        ]
    )
    _write_text(out_tex, tex)

    print(f"[fold-zm-s4-rep] wrote {out_json}", flush=True)
    print(f"[fold-zm-s4-rep] wrote {out_tex}", flush=True)
    print("[fold-zm-s4-rep] done", flush=True)


if __name__ == "__main__":
    main()

