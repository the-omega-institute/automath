#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Canonical Z_34 indexing and real Fourier (DFT) decomposition of the m=11 boundary layer.

All code is English-only by repository convention.

Manuscript context:
  - Boundary sector at resolution m (endpoint-(1,1) fiber):
        X_m^{bdry} := { u in X_m : u_1=1 and u_m=1 },  |X_m^{bdry}| = F_{m-2}.
  - For m=11, |X_11^{bdry}| = F_9 = 34.
  - There is a canonical bijection X_11^{bdry} <-> X_7 by stripping/adding the forced
    endpoint pattern "10" ... "01":
        v in X_7  <->  u = 10 v 01 in X_11^{bdry}.
  - By labeling v in X_7 via its Zeckendorf value coordinate j in {0,...,F_9-1},
    we obtain a canonical indexing j in Z_34 of the 34 boundary modes.

On R^{34} with basis (e_j)_{j in Z_34}, define the shift action:
  T(e_j) = e_{j+1}  (mod 34).
Then the real representation decomposes as:
  34 = 1 ⊕ 1 ⊕ 16×2,
where the 1's are the invariant (k=0) and sign (k=17) directions, and the 16 pairs
are the (cos_k, sin_k) rotation planes (k=1..16).

Outputs:
  - artifacts/export/m11_boundary_z34_fourier_decomposition.json
  - sections/generated/eq_m11_boundary_z34_decomposition.tex
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import fib_upto, is_golden_legal, word_to_str, zeckendorf_digits


def _golden_words(m: int) -> List[str]:
    """All length-m binary words with no adjacent ones (golden mean SFT), sorted."""
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
    return sorted(word_to_str(w) for w in out)


def _canonical_Xm_by_value(m: int) -> List[str]:
    """Canonical ordering j -> Zeckendorf digits of j, for j in [0..F_{m+2}-1]."""
    if m < 0:
        raise ValueError("m must be non-negative")
    if m == 0:
        return [""]
    M = int(fib_upto(m + 2)[-1])  # F_{m+2}
    words: List[str] = []
    for j in range(M):
        w = word_to_str(zeckendorf_digits(int(j), int(m)))
        if not is_golden_legal([1 if ch == "1" else 0 for ch in w]):
            raise AssertionError(f"Non-legal word produced by Zeckendorf digits: m={m} j={j} w={w}")
        words.append(w)
    if len(set(words)) != len(words):
        raise AssertionError(f"Canonical j->X_m map is not injective for m={m}")
    return words


def _u11_from_v7(v7: str) -> str:
    if len(v7) != 7:
        raise ValueError("v7 must have length 7")
    u = "10" + v7 + "01"
    if len(u) != 11:
        raise AssertionError("bad length for u11")
    # Check golden legality and boundary endpoints.
    if u[0] != "1" or u[-1] != "1":
        raise AssertionError("u11 is not boundary (endpoints not 1)")
    if "11" in u:
        raise AssertionError(f"u11 is not golden-legal: {u}")
    return u


def _shift_matrix(N: int) -> np.ndarray:
    """Permutation matrix T with T e_j = e_{j+1} (mod N)."""
    T = np.zeros((N, N), dtype=np.float64)
    for j in range(N):
        T[(j + 1) % N, j] = 1.0
    return T


def _real_fourier_basis(N: int) -> Tuple[List[np.ndarray], Dict[str, object]]:
    """
    Return (basis, info), where basis is ordered as:
      [Y0, Yhalf, C1, S1, ..., C_{N/2-1}, S_{N/2-1}]
    for even N.
    """
    if N % 2 != 0:
        raise ValueError("This script assumes even N")
    j = np.arange(N, dtype=np.float64)

    basis: List[np.ndarray] = []
    Y0 = np.ones(N, dtype=np.float64) / math.sqrt(float(N))
    basis.append(Y0)

    # k=N/2 (self-conjugate): (-1)^j
    Yhalf = ((-1.0) ** j) / math.sqrt(float(N))
    basis.append(Yhalf)

    # k=1..(N/2-1): cosine/sine planes.
    scale = math.sqrt(2.0 / float(N))
    for k in range(1, N // 2):
        ang = (2.0 * math.pi * float(k) / float(N)) * j
        Ck = scale * np.cos(ang)
        Sk = scale * np.sin(ang)
        basis.append(Ck)
        basis.append(Sk)

    B = np.stack(basis, axis=1)  # columns are basis vectors
    G = B.T @ B
    ortho_err = float(np.max(np.abs(G - np.eye(N))))

    order: List[str] = ["Y0", "Y17"]
    for k in range(1, N // 2):
        order.extend([f"C{k}", f"S{k}"])

    info: Dict[str, object] = {
        "N": int(N),
        "basis_order": order,
        "orthonormal_max_abs_error": ortho_err,
    }
    return basis, info


def _verify_shift_rotation(N: int, basis: Sequence[np.ndarray]) -> float:
    """
    Verify that the shift acts as:
      - Y0 invariant
      - Yhalf -> -Yhalf
      - (Ck,Sk) rotates by angle 2πk/N
    Return max absolute error over all checked identities.
    """
    T = _shift_matrix(N)
    err = 0.0

    # Y0
    Y0 = basis[0]
    err = max(err, float(np.max(np.abs(T @ Y0 - Y0))))

    # Yhalf
    Yh = basis[1]
    err = max(err, float(np.max(np.abs(T @ Yh + Yh))))

    # k=1..N/2-1
    idx = 2
    for k in range(1, N // 2):
        Ck = basis[idx]
        Sk = basis[idx + 1]
        idx += 2
        theta = 2.0 * math.pi * float(k) / float(N)
        c = math.cos(theta)
        s = math.sin(theta)
        # T*Ck = c*Ck + s*Sk;  T*Sk = -s*Ck + c*Sk
        err = max(err, float(np.max(np.abs((T @ Ck) - (c * Ck + s * Sk)))))
        err = max(err, float(np.max(np.abs((T @ Sk) - (-s * Ck + c * Sk)))))
    return float(err)


def _write_tex(path: Path) -> None:
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_m11_boundary_z34_fourier_decomposition.py")
    lines.append("\\[")
    lines.append("\\begin{aligned}")
    lines.append("&|X_{11}^{\\mathrm{bdry}}|=F_9=34,\\qquad X_{11}^{\\mathrm{bdry}}\\cong X_7,\\quad u=10\\,v\\,01,\\\\")
    lines.append("&\\RR^{34}=\\Span\\{Y_0\\}\\oplus\\Span\\{Y_{17}\\}\\oplus\\bigoplus_{k=1}^{16}\\Span\\{C_k,S_k\\},\\\\")
    lines.append("&Y_0:=\\frac{1}{\\sqrt{34}}\\sum_{j=0}^{33}e_j,\\qquad")
    lines.append("Y_{17}:=\\frac{1}{\\sqrt{34}}\\sum_{j=0}^{33}(-1)^j e_j,\\\\")
    lines.append("&C_k:=\\sqrt{\\frac{2}{34}}\\sum_{j=0}^{33}\\cos\\!\\left(\\frac{2\\pi k j}{34}\\right)e_j,\\qquad")
    lines.append("S_k:=\\sqrt{\\frac{2}{34}}\\sum_{j=0}^{33}\\sin\\!\\left(\\frac{2\\pi k j}{34}\\right)e_j,\\quad 1\\le k\\le 16,\\\\")
    lines.append("&34=1\\oplus 33,\\qquad 33=1\\oplus 16\\times 2.")
    lines.append("\\end{aligned}")
    lines.append("\\]")
    lines.append("")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Canonical Z_34 indexing and real Fourier decomposition for m=11 boundary.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "m11_boundary_z34_fourier_decomposition.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_m11_boundary_z34_decomposition.tex"),
    )
    args = ap.parse_args()

    # Canonical X7 ordering by value coordinate j in [0..F9-1].
    X7_by_value = _canonical_Xm_by_value(7)
    if len(X7_by_value) != 34:
        raise AssertionError(f"Expected |X7|=34, got {len(X7_by_value)}")

    # Cross-check: equals the full golden-legal set X7.
    X7_all = _golden_words(7)
    if set(X7_by_value) != set(X7_all):
        missing = sorted(list(set(X7_all) - set(X7_by_value)))[:10]
        extra = sorted(list(set(X7_by_value) - set(X7_all)))[:10]
        raise AssertionError(f"Canonical X7_by_value != X7_all. missing={missing} extra={extra}")

    indexing: List[Dict[str, object]] = []
    for j, v7 in enumerate(X7_by_value):
        u11 = _u11_from_v7(v7)
        indexing.append({"j": int(j), "v7": v7, "u11": u11})

    # Real Fourier basis and audit checks.
    N = 34
    basis, info = _real_fourier_basis(N)
    shift_err = _verify_shift_rotation(N, basis=basis)
    info["shift_rotation_max_abs_error"] = float(shift_err)

    # Assemble JSON (audit-friendly, small).
    payload: Dict[str, object] = {
        "params": {"m_boundary": 11, "m_stable": 7, "N": N},
        "counts": {
            "|X_11_bdry|": int(fib_upto(9)[-1]),
            "|X_7|": int(fib_upto(9)[-1]),
        },
        "canonical_indexing": indexing,
        "real_fourier_decomposition": {
            "decomposition_dims": {"trivial": 1, "sign": 1, "pairs": 16, "pair_dim": 2, "total": 34},
            "checks": info,
        },
    }

    json_out = Path(args.json_out)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    _write_tex(Path(args.tex_out))

    print(f"[m11-z34] wrote {args.tex_out}", flush=True)
    print(f"[m11-z34] wrote {args.json_out}", flush=True)


if __name__ == "__main__":
    main()

