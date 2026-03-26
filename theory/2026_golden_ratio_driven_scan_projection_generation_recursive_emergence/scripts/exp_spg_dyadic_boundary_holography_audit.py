#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit dyadic cubical boundary injectivity and boundary->bulk reconstruction.

This script provides a finite-size certificate for Theorem:
  - top-dimensional boundary map ∂_n is injective for the dyadic cubical complex of I^n,
  - given a polycube U (0/1 n-chain), its boundary determines U uniquely.

We verify injectivity over Q by computing rank(∂_n) = #n-cubes for small (n,m),
and we reconstruct random polycubes from their boundary via normal equations:
  (∂^T ∂) x = ∂^T b.

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import random
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import paper_root, scripts_dir


@dataclass(frozen=True)
class CaseResult:
    n: int
    m: int
    n_cubes: int
    n1_faces_oriented: int
    boundary_rank: int
    injective: bool
    reconstruction_trials: int
    reconstruction_ok: bool


def _cube_cells(n: int, m: int) -> List[Tuple[int, ...]]:
    """List n-cubes as integer grid coordinates (lower corner) in {0,...,2^m-1}^n."""
    L = 1 << m
    cubes: List[Tuple[int, ...]] = []
    for idx in range(L**n):
        coord: List[int] = []
        x = idx
        for _ in range(n):
            coord.append(x % L)
            x //= L
        cubes.append(tuple(coord))
    return cubes


def _oriented_faces(n: int, m: int) -> List[Tuple[int, Tuple[int, ...]]]:
    """
    Oriented (n-1)-faces are represented as (axis, anchor),
    where axis in {0,...,n-1} is the normal direction, and anchor is an n-tuple
    with anchor[axis] in {0,...,2^m} (face hyperplane position) and others in {0,...,2^m-1}.

    Orientation convention:
      axis = i means face is orthogonal to e_i, oriented by increasing x_i.
      A cube at lower corner c contributes:
        + to face at anchor with anchor[i]=c[i]+1 (positive side),
        - to face at anchor with anchor[i]=c[i]   (negative side).
    """
    L = 1 << m
    faces: List[Tuple[int, Tuple[int, ...]]] = []
    for axis in range(n):
        # other coordinates in 0..L-1, axis coordinate in 0..L
        for idx in range((L + 1) * (L ** (n - 1))):
            anchor: List[int] = [0] * n
            x = idx
            for j in range(n):
                if j == axis:
                    anchor[j] = x % (L + 1)
                    x //= (L + 1)
                else:
                    anchor[j] = x % L
                    x //= L
            faces.append((axis, tuple(anchor)))
    return faces


def _boundary_matrix(n: int, m: int) -> sp.Matrix:
    """Return boundary matrix ∂_n as an (oriented faces) x (n-cubes) integer matrix."""
    cubes = _cube_cells(n, m)
    faces = _oriented_faces(n, m)
    face_index: Dict[Tuple[int, Tuple[int, ...]], int] = {f: i for i, f in enumerate(faces)}

    rows = len(faces)
    cols = len(cubes)
    M = sp.zeros(rows, cols)

    for j, c in enumerate(cubes):
        for axis in range(n):
            # negative face at anchor[axis]=c[axis]
            anchor_neg = list(c)
            anchor_neg[axis] = c[axis]
            fneg = (axis, tuple(anchor_neg))
            # positive face at anchor[axis]=c[axis]+1
            anchor_pos = list(c)
            anchor_pos[axis] = c[axis] + 1
            fpos = (axis, tuple(anchor_pos))
            M[face_index[fpos], j] += 1
            M[face_index[fneg], j] -= 1
    return M


def _reconstruct_from_boundary(M: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
    """Solve M x = b with full column-rank M using normal equations."""
    MT = M.T
    A = MT * M
    rhs = MT * b
    return A.LUsolve(rhs)


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit dyadic boundary injectivity and reconstruction.")
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(paper_root() / "artifacts" / "export" / "spg_dyadic_boundary_holography_audit.json"),
        help="Output JSON path.",
    )
    parser.add_argument("--seed", type=int, default=0, help="RNG seed for reconstruction trials.")
    args = parser.parse_args()

    random.seed(args.seed)

    cases = [(2, 1), (2, 2), (3, 1), (3, 2)]
    results: List[CaseResult] = []

    for n, m in cases:
        M = _boundary_matrix(n, m)
        boundary_rank = int(M.rank())  # rank over Q
        n_cubes = int(M.shape[1])
        n_faces = int(M.shape[0])
        injective = boundary_rank == n_cubes

        # Reconstruction trials
        trials = 10
        ok = True
        for _ in range(trials):
            x = sp.Matrix([sp.Integer(random.randint(0, 1)) for _ in range(n_cubes)])
            b = M * x
            x_hat = _reconstruct_from_boundary(M, b)
            if sp.simplify(x_hat - x) != sp.zeros(n_cubes, 1):
                ok = False
                break

        results.append(
            CaseResult(
                n=n,
                m=m,
                n_cubes=n_cubes,
                n1_faces_oriented=n_faces,
                boundary_rank=boundary_rank,
                injective=injective,
                reconstruction_trials=trials,
                reconstruction_ok=ok,
            )
        )

    out: Dict[str, object] = {
        "cases": [asdict(r) for r in results],
        "meta": {
            "script": Path(__file__).name,
            "scripts_dir": str(scripts_dir()),
        },
    }

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Hard assertions for pipeline gating
    for r in results:
        assert r.injective, f"Boundary map not injective for n={r.n}, m={r.m}"
        assert r.reconstruction_ok, f"Reconstruction failed for n={r.n}, m={r.m}"


if __name__ == "__main__":
    main()

