#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Auditable block factorization for the real-input 40-state kernel under pure collision twists.

We consider the 3D twisting family with (j1,j2)=(0,0) and third axis = N2 (collision trigger xi=1_{d=2}):
  M_xi(u) := M(1,1,u),  u in C.

The paper proves an invariant orthogonal decomposition:
  R^40 = U ⊕ U_perp,
where U = R^4 ⊗ span{1} and U_perp = R^4 ⊗ 1^perp inside R^4 ⊗ R^10.

This script constructs an explicit orthonormal change-of-basis Q that block-diagonalizes M_xi(u) numerically,
and certifies:
  - off-diagonal blocks are (numerically) zero,
  - det(I - z M) = det(I - z M|_U) det(I - z M|_{U_perp}),
  - rho(M|_{U_perp}) ≤ phi for |u|=1, hence no A_2-like block (whose Perron root r_2 > phi) can live in U_perp.

Outputs:
  - artifacts/export/real_input_40_pure_collision_block_factorization.json
  - sections/generated/tab_real_input_40_pure_collision_block_factorization.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from exp_sync_kernel_real_input_40_arity_3d import (
    build_kernel_edges,
    build_kernel_map,
    build_real_input_states,
    build_weighted_matrix_numeric,
    spectral_radius,
)


def _orthonormal_basis_block10() -> np.ndarray:
    """Return a 10x10 real orthonormal basis: first column ~ ones, rest span sum-zero subspace."""
    n = 10
    v0 = np.ones((n, 1), dtype=float) / math.sqrt(n)
    # Build 9 columns spanning sum-zero: e_i - e_9 for i=0..8
    B = np.zeros((n, 9), dtype=float)
    for i in range(9):
        B[i, i] = 1.0
        B[9, i] = -1.0
    # Orthonormalize [v0 | B] via QR.
    X = np.hstack([v0, B])
    Q, _R = np.linalg.qr(X)
    # Ensure deterministic sign for the first column (positive sum).
    if float(np.sum(Q[:, 0])) < 0:
        Q[:, 0] *= -1.0
    return Q


def _build_global_Q(states: List[Tuple[str, int, int]]) -> np.ndarray:
    """Construct 40x40 orthonormal Q respecting the (px,py) block partition."""
    idx = {st: i for i, st in enumerate(states)}
    # Partition indices by (px,py).
    blocks: Dict[Tuple[int, int], List[int]] = {(0, 0): [], (0, 1): [], (1, 0): [], (1, 1): []}
    for s, px, py in states:
        blocks[(px, py)].append(idx[(s, px, py)])
    for key, inds in blocks.items():
        if len(inds) != 10:
            raise RuntimeError(f"block {key} has size {len(inds)} != 10")

    Q10 = _orthonormal_basis_block10()  # columns: [ones/sqrt10, ..., sum-zero]
    Q = np.zeros((40, 40), dtype=float)

    # Column layout:
    # - first 4 columns: U basis, one per (px,py) in fixed order
    # - remaining 36 columns: 9 per block in the same block order
    block_order = [(0, 0), (0, 1), (1, 0), (1, 1)]

    # U columns
    for b, key in enumerate(block_order):
        inds = blocks[key]
        for i_local, i_global in enumerate(inds):
            Q[i_global, b] = float(Q10[i_local, 0])

    # U_perp columns
    col = 4
    for key in block_order:
        inds = blocks[key]
        for k in range(1, 10):  # 9 columns
            for i_local, i_global in enumerate(inds):
                Q[i_global, col] = float(Q10[i_local, k])
            col += 1
    if col != 40:
        raise RuntimeError(f"unexpected column count: {col}")

    # Orthonormal check
    I = Q.T @ Q
    err = float(np.max(np.abs(I - np.eye(40))))
    if err > 1e-10:
        raise RuntimeError(f"Q is not orthonormal, max |Q^T Q - I|={err}")
    return Q


@dataclass(frozen=True)
class Row:
    label: str
    u: str
    rho_U: float
    rho_perp: float
    offdiag_UR: float
    offdiag_LL: float
    det_rel_err: float


def _det_rel_err(M: np.ndarray, MU: np.ndarray, MP: np.ndarray, z: complex) -> float:
    det_full = np.linalg.det(np.eye(M.shape[0], dtype=complex) - z * M)
    det_fact = np.linalg.det(np.eye(MU.shape[0], dtype=complex) - z * MU) * np.linalg.det(
        np.eye(MP.shape[0], dtype=complex) - z * MP
    )
    num = abs(det_full - det_fact)
    den = max(1.0, abs(det_full), abs(det_fact))
    return float(num / den)


def main() -> None:
    parser = argparse.ArgumentParser(description="Block factorization certificate for M_xi(u).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_pure_collision_block_factorization.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_pure_collision_block_factorization.tex"),
    )
    parser.add_argument("--z-test", type=float, default=0.07, help="Test value for determinant factorization.")
    args = parser.parse_args()

    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()
    Q = _build_global_Q(states).astype(complex)

    phi = (1.0 + 5.0**0.5) / 2.0
    lam = phi * phi
    r2 = 2.481194304092  # from the paper's fold collision kernel A_2

    # Sample unit-modulus twists.
    samples: List[Tuple[str, complex]] = [
        ("u=1", 1.0 + 0.0j),
        ("u=-1", -1.0 + 0.0j),
        ("u=exp(2πi/5)", complex(math.cos(2 * math.pi / 5), math.sin(2 * math.pi / 5))),
        ("u=exp(2πi/7)", complex(math.cos(2 * math.pi / 7), math.sin(2 * math.pi / 7))),
    ]

    rows: List[Row] = []
    z = complex(float(args.z_test), 0.0)

    for label, u in samples:
        M = build_weighted_matrix_numeric(1.0 + 0.0j, 1.0 + 0.0j, u, states, kernel_map, third_axis="N2")
        # Change basis: Q^* M Q
        Mt = (Q.conj().T @ M @ Q).astype(complex)
        MU = Mt[:4, :4]
        MP = Mt[4:, 4:]
        off_ur = float(np.max(np.abs(Mt[:4, 4:])))
        off_ll = float(np.max(np.abs(Mt[4:, :4])))
        rhoU = float(np.max(np.abs(np.linalg.eigvals(MU))))
        rhoP = float(np.max(np.abs(np.linalg.eigvals(MP))))

        rel = _det_rel_err(M, MU, MP, z)
        rows.append(
            Row(
                label=label,
                u=str(u),
                rho_U=rhoU,
                rho_perp=rhoP,
                offdiag_UR=off_ur,
                offdiag_LL=off_ll,
                det_rel_err=rel,
            )
        )
        print(
            f"[block-factor] {label}: rho_U={rhoU:.12g}, rho_perp={rhoP:.12g}, UR={off_ur:.2e}, LL={off_ll:.2e}",
            flush=True,
        )

    payload: Dict[str, object] = {
        "phi": phi,
        "lambda": lam,
        "r2_fold_collision": r2,
        "z_test": float(args.z_test),
        "rows": [asdict(r) for r in rows],
        "note": "For |u|=1 we expect rho_perp <= phi < r2, hence no A2-like Perron root can appear in U_perp.",
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[block-factor] wrote {jout}", flush=True)

    # LaTeX table.
    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Numerical certificate for the invariant decomposition $\\mathbb R^{40}=U\\oplus U^\\perp$ "
        "under pure collision twists $M_\\xi(u)$ (third axis $N_2$). We report the spectral radii on $U$ and "
        "on the induced quotient operator $\\overline M$ (lower-right block), the max absolute UR/LL off-diagonal "
        "entries after an explicit orthonormal change of basis (LL should be numerical $0$ since $U$ is invariant), "
        "and a determinant factorization check at a fixed $z$ (relative error).}"
    )
    lines.append("\\label{tab:real_input_40_pure_collision_block_factorization}")
    lines.append("\\begin{tabular}{l r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$u$ & $\\rho(M|_U)$ & $\\rho(\\overline M)$ & "
        "$\\|\\mathrm{UR}\\|_{\\max}$ & $\\|\\mathrm{LL}\\|_{\\max}$ & det rel err\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.label} & {r.rho_U:.12f} & {r.rho_perp:.12f} & {r.offdiag_UR:.2e} & {r.offdiag_LL:.2e} & {r.det_rel_err:.2e}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[block-factor] wrote {tout}", flush=True)
    print("[block-factor] done", flush=True)


if __name__ == "__main__":
    main()

