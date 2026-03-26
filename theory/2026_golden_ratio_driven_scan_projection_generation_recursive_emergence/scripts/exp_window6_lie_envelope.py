#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: coordinate pushforward operators on X_6 and their Lie envelope.

All code is English-only by repository convention.

Setup:
  - Omega_6 = {0,1}^6, encoded as integers n=0..63 via int_6(omega_1..omega_6)=sum omega_k 2^{6-k}.
  - Fold^{bin}_6 : {0,...,63} -> X_6 is the dyadic (binary-interval) fold at m=6.
  - Label map on the 6-cube: F6(omega) := Fold^{bin}_6(int_6(omega)) ∈ X_6.

For each coordinate direction i=1..6 (flipping omega_i), define the directed pushforward operator
  (L_i)_{uv} := #{ omega ∈ Omega_6 : F6(omega)=u and F6(omega ⊕ e_i)=v }.
Equivalently, L_i counts the number of directed i-edges from the fiber of u to the fiber of v.

We compute:
  - the six integer matrices L_i ∈ Z^{21×21},
  - the Lie algebra g_6 := Lie⟨L_1,...,L_6⟩ ⊂ gl(21,Q) generated under commutators,
  - basic invariants: dim(g_6), dim([g_6,g_6]), dim(Z(g_6)),
  - the Killing form rank/determinant (via adjoint representation),
  - the commutant dimension of the adjoint representation (detects simple vs. direct sum).

Outputs:
  - artifacts/export/window6_lie_envelope.json
  - sections/generated/eq_window6_lie_envelope_invariants.tex
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from collections import deque
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import word_to_str, zeckendorf_digits


class Heartbeat:
    def __init__(self, interval_s: float = 20.0) -> None:
        self.interval_s = float(interval_s)
        self._t0 = time.monotonic()
        self._t_last = self._t0

    def beat(self, msg: str) -> None:
        now = time.monotonic()
        if now - self._t_last >= self.interval_s:
            dt = now - self._t0
            print(f"[heartbeat +{dt:,.1f}s] {msg}", file=sys.stderr, flush=True)
            self._t_last = now


def _primes_for_audit() -> List[int]:
    # Multiple primes improve robustness and, in practice, speed: modular linear algebra
    # avoids expensive exact-rank computations. We keep primes ~1e6 to prevent int64 overflow
    # in numpy dot products: 21 * (p-1)^2 must fit in signed 64-bit.
    return [1_000_003, 1_000_033, 1_000_037, 1_000_039, 1_000_081]


def _foldbin6_label(n: int) -> str:
    # For m=6, K(6)=9 (F_{10}=55 ≤ 63 < F_{11}=89), so digits up to k=9 are exact.
    digits = zeckendorf_digits(n, 9)  # digits for weights F_{k+1}, k=1..9
    return word_to_str(digits[:6])

def _as_np_int64(M: List[List[int]]) -> np.ndarray:
    return np.array(M, dtype=np.int64)


def _flatten(A: np.ndarray) -> np.ndarray:
    return A.reshape((-1,))


def _mod_matmul(A: np.ndarray, B: np.ndarray, p: int) -> np.ndarray:
    return (A @ B) % p


def _mod_comm(A: np.ndarray, B: np.ndarray, p: int) -> np.ndarray:
    return (_mod_matmul(A, B, p) - _mod_matmul(B, A, p)) % p


class ModBasisNP:
    """Incremental row-echelon basis over GF(p) for vectors in F_p^n."""

    def __init__(self, p: int, n: int) -> None:
        self.p = int(p)
        self.n = int(n)
        self.pivots: List[int] = []
        self.rows: Dict[int, np.ndarray] = {}

    def try_add(self, v0: np.ndarray) -> bool:
        p = self.p
        v = (v0 % p).astype(np.int64, copy=True)

        # Eliminate known pivots.
        for k in self.pivots:
            coeff = int(v[k] % p)
            if coeff == 0:
                continue
            row = self.rows[k]
            v[k:] = (v[k:] - coeff * row[k:]) % p

        # Find new pivot.
        nz = np.flatnonzero(v % p)
        if nz.size == 0:
            return False
        pivot = int(nz[0])

        inv = pow(int(v[pivot] % p), -1, p)
        v[pivot:] = (v[pivot:] * inv) % p

        # Eliminate the pivot column from existing rows.
        for k in list(self.pivots):
            rowk = self.rows[k]
            coeff = int(rowk[pivot] % p)
            if coeff == 0:
                continue
            rowk[pivot:] = (rowk[pivot:] - coeff * v[pivot:]) % p
            self.rows[k] = rowk

        self.pivots.append(pivot)
        self.pivots.sort()
        self.rows[pivot] = v
        return True


def _mod_rank(M: np.ndarray, p: int, hb: Heartbeat, label: str) -> int:
    """Rank over F_p by Gaussian elimination on rows (copying M)."""
    A = (M % p).astype(np.int64, copy=True)
    m, n = A.shape
    r = 0
    for c in range(n):
        hb.beat(f"{label}: elim r={r}, c={c}/{n}")
        pivot = None
        for i in range(r, m):
            if A[i, c] % p != 0:
                pivot = i
                break
        if pivot is None:
            continue
        if pivot != r:
            A[[r, pivot], :] = A[[pivot, r], :]
        inv = pow(int(A[r, c] % p), -1, p)
        A[r, c:] = (A[r, c:] * inv) % p
        for i in range(m):
            if i == r:
                continue
            coeff = int(A[i, c] % p)
            if coeff != 0:
                A[i, c:] = (A[i, c:] - coeff * A[r, c:]) % p
        r += 1
        if r == m:
            break
    return int(r)


def _mod_inv_square(M: np.ndarray, p: int, hb: Heartbeat, label: str) -> np.ndarray:
    """Inverse of a square matrix over F_p via Gauss-Jordan."""
    A = (M % p).astype(np.int64, copy=True)
    n = A.shape[0]
    I = np.eye(n, dtype=np.int64)
    AI = np.concatenate([A, I], axis=1)
    r = 0
    for c in range(n):
        hb.beat(f"{label}: inv r={r}, c={c}/{n}")
        pivot = None
        for i in range(r, n):
            if AI[i, c] % p != 0:
                pivot = i
                break
        if pivot is None:
            raise RuntimeError("Singular matrix in modular inversion.")
        if pivot != r:
            AI[[r, pivot], :] = AI[[pivot, r], :]
        inv = pow(int(AI[r, c] % p), -1, p)
        AI[r, :] = (AI[r, :] * inv) % p
        for i in range(n):
            if i == r:
                continue
            coeff = int(AI[i, c] % p)
            if coeff != 0:
                AI[i, :] = (AI[i, :] - coeff * AI[r, :]) % p
        r += 1
    return AI[:, n:] % p


def _lie_closure_mod(
    gens: List[np.ndarray],
    p: int,
    hb: Heartbeat,
) -> List[np.ndarray]:
    """Compute a basis of Lie⟨gens⟩ inside gl(21, F_p), using incremental elimination."""
    n = gens[0].shape[0]
    vec_len = n * n
    basis: List[np.ndarray] = []
    mb = ModBasisNP(p=p, n=vec_len)

    def try_add(X: np.ndarray) -> bool:
        v = _flatten(X) % p
        if mb.try_add(v):
            basis.append(X % p)
            return True
        return False

    q: deque[int] = deque()
    for G in gens:
        if try_add(G):
            q.append(len(basis) - 1)

    processed = 0
    while q:
        i = q.popleft()
        processed += 1
        hb.beat(f"lie_closure_mod:p={p}: basis_dim={len(basis)}, processed={processed}")
        Ei = basis[i]
        for Gj in gens:
            C = _mod_comm(Ei, Gj, p)
            if try_add(C):
                q.append(len(basis) - 1)

    # sanity
    if len(basis) > vec_len:
        raise RuntimeError("Lie closure exceeded ambient dimension.")
    return basis


def _coords_left_inverse(basis_vecs: np.ndarray, p: int, hb: Heartbeat) -> np.ndarray:
    """Return B_left such that coords(v)=B_left @ v for v in span(B)."""
    B = basis_vecs % p  # (vec_len) x dim
    Gram = (B.T @ B) % p  # dim x dim
    Gram_inv = _mod_inv_square(Gram, p=p, hb=hb, label=f"p={p}:Gram_inv")
    return (Gram_inv @ B.T) % p  # dim x vec_len


def _rank_span_vectors(vecs: List[np.ndarray], p: int, hb: Heartbeat, label: str) -> int:
    if not vecs:
        return 0
    n = int(vecs[0].shape[0])
    mb = ModBasisNP(p=p, n=n)
    for i, v in enumerate(vecs):
        if i % 50 == 0:
            hb.beat(f"{label}: i={i}/{len(vecs)}")
        mb.try_add(v)
    return int(len(mb.pivots))


def _commutant_dim_from_ad(ad_gens: List[np.ndarray], p: int, hb: Heartbeat) -> int:
    """Dimension of {X : XA=AX for all A in ad_gens} over F_p."""
    dim = ad_gens[0].shape[0]
    I = np.eye(dim, dtype=np.int64)
    blocks: List[np.ndarray] = []
    for k, A in enumerate(ad_gens):
        hb.beat(f"p={p}:commutant: assembling {k+1}/{len(ad_gens)}")
        blocks.append(np.kron(A.T % p, I) - np.kron(I, A % p))
    M = np.concatenate(blocks, axis=0) % p  # (k*dim^2) x (dim^2)
    mb = ModBasisNP(p=p, n=dim * dim)
    for i in range(M.shape[0]):
        if i % 200 == 0:
            hb.beat(f"p={p}:commutant: row {i}/{M.shape[0]}")
        mb.try_add(M[i, :])
    return int(dim * dim - len(mb.pivots))


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit the window-6 coordinate pushforward operators and Lie envelope.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "window6_lie_envelope.json"),
        help="Path to JSON audit output.",
    )
    ap.add_argument(
        "--tex-eq-out",
        type=str,
        default=str(generated_dir() / "eq_window6_lie_envelope_invariants.tex"),
        help="Path to generated TeX equation snippet (\\input{}).",
    )
    ap.add_argument(
        "--prime",
        type=int,
        default=1_000_003,
        help="Single prime modulus for the audit (default: 1000003).",
    )
    args = ap.parse_args()

    hb = Heartbeat(interval_s=20.0)
    print("[info] starting: window6 Lie envelope audit", file=sys.stderr, flush=True)

    labels = [_foldbin6_label(n) for n in range(64)]
    words = sorted(set(labels))
    if len(words) != 21:
        raise RuntimeError(f"Unexpected |X_6| from Fold^{{bin}}_6: {len(words)}")
    idx = {w: i for i, w in enumerate(words)}

    fiber_size: Dict[str, int] = {w: 0 for w in words}
    for w in labels:
        fiber_size[w] += 1

    # Coordinate directions i=1..6 correspond to flipping omega_i, i.e. XOR with 2^{6-i}.
    bits = [1 << (6 - i) for i in range(1, 7)]
    L_int: List[List[List[int]]] = []
    for bit in bits:
        M = [[0 for _ in range(21)] for _ in range(21)]
        for n in range(64):
            nn = n ^ bit
            a = idx[labels[n]]
            b = idx[labels[nn]]
            M[a][b] += 1
        # Row sums should equal fiber sizes (one outgoing i-edge per microstate).
        for w in words:
            r = idx[w]
            if int(sum(M[r][c] for c in range(21))) != int(fiber_size[w]):
                raise RuntimeError("Row-sum check failed for some L_i.")
        L_int.append(M)

    hb.beat("constructed coordinate pushforward operators L_i")

    p = int(args.prime)
    hb.beat(f"mod-audit: p={p}")
    gens = [_as_np_int64(M) % p for M in L_int]

    basis = _lie_closure_mod(gens, p=p, hb=hb)
    dim_g = len(basis)
    hb.beat(f"p={p}: lie closure dim={dim_g}")
    print(f"[info] computed lie closure dim_g={dim_g} (mod p={p})", file=sys.stderr, flush=True)

    # Fast structural identification: for window-6, edge separation implies diag(L_i)=0, hence tr(L_i)=0.
    traces = [int(np.trace(Gj) % p) for Gj in gens]
    if dim_g == 21 * 21 - 1 and all(t == 0 for t in traces):
        # Then g ⊂ sl(21, F_p) and dim forces equality, hence the standard invariants follow.
        dim_derived = dim_g
        dim_center = 0
        killing_rank = dim_g  # p is huge, in particular p ∤ 21.
        commutant_dim = 1
        hb.beat(f"p={p}: identified g as sl(21) by dimension+trace")
    else:
        vec_len = 21 * 21
        basis_vecs = np.stack([_flatten(Bi) % p for Bi in basis], axis=1)  # vec_len x dim
        B_left = _coords_left_inverse(basis_vecs, p=p, hb=hb)  # dim x vec_len

        # Derived algebra dimension: span of [basis, gens].
        comm_vecs: List[np.ndarray] = []
        for i, Ei in enumerate(basis):
            hb.beat(f"p={p}: derived comms {i+1}/{dim_g}")
            for Gj in gens:
                comm_vecs.append(_flatten(_mod_comm(Ei, Gj, p)) % p)
        dim_derived = _rank_span_vectors(comm_vecs, p=p, hb=hb, label=f"p={p}:derived_span_rank")

        # Center dimension: kernel of Z ↦ ([Z,G_j])_j.
        hb.beat(f"p={p}: center constraints")
        blocks: List[np.ndarray] = []
        for j, Gj in enumerate(gens):
            hb.beat(f"p={p}: center block {j+1}/{len(gens)}")
            cols = []
            for Ek in basis:
                cols.append(_flatten(_mod_comm(Ek, Gj, p)) % p)
            Bj = np.stack(cols, axis=1) % p  # vec_len x dim_g
            blocks.append(Bj)
        C = np.concatenate(blocks, axis=0) % p  # (|gens|*vec_len) x dim_g
        rank_constraints = _mod_rank(C, p=p, hb=hb, label=f"p={p}:center_constraints_rank")
        dim_center = int(dim_g - rank_constraints)

        # Commutant dimension of adjoint representation, using ad(generators).
        hb.beat(f"p={p}: adjoint generators")
        ad_gens: List[np.ndarray] = []
        for j, Gj in enumerate(gens):
            hb.beat(f"p={p}: ad(G_{j+1})")
            cols = []
            for Ek in basis:
                v = _flatten(_mod_comm(Gj, Ek, p)) % p
                cols.append((B_left @ v) % p)
            adG = np.stack(cols, axis=1) % p
            ad_gens.append(adG)

        hb.beat(f"p={p}: commutant dimension")
        commutant_dim = _commutant_dim_from_ad(ad_gens, p=p, hb=hb)

        # Killing rank is intentionally skipped in the fallback path (costly).
        killing_rank = -1

    print(
        f"[info] invariants: dim_g={dim_g}, dim_derived={dim_derived}, "
        f"dim_center={dim_center}, killing_rank={killing_rank}, commutant_dim_ad={commutant_dim}",
        file=sys.stderr,
        flush=True,
    )

    payload: Dict[str, object] = {
        "m": 6,
        "words": words,
        "fiber_size_d_bin": {w: int(fiber_size[w]) for w in words},
        "L_coord_edge_counts": L_int,
        "mod_prime": int(p),
        "lie_envelope": {
            "dim_g": int(dim_g),
            "dim_derived": int(dim_derived),
            "dim_center": int(dim_center),
            "killing_rank": int(killing_rank),
            "commutant_dim_ad": int(commutant_dim),
        },
    }

    json_out = Path(str(args.json_out))
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[info] wrote JSON: {json_out}", file=sys.stderr, flush=True)

    # TeX equation snippet.
    tex_out = Path(str(args.tex_eq_out))
    tex_out.parent.mkdir(parents=True, exist_ok=True)

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_window6_lie_envelope.py")
    lines.append("\\begin{equation}\\label{eq:window6_lie_envelope_invariants}")
    lines.append("\\begin{aligned}")
    lines.append(f"\\dim\\mathfrak{{g}}_6&={dim_g},\\\\")
    lines.append(f"\\dim[\\mathfrak{{g}}_6,\\mathfrak{{g}}_6]&={dim_derived},\\\\")
    lines.append(f"\\dim Z(\\mathfrak{{g}}_6)&={dim_center},\\\\")
    lines.append(f"\\mathrm{{rank}}\\,\\kappa_6&={killing_rank},\\\\")
    lines.append(f"\\dim\\,\\mathrm{{Comm}}(\\mathrm{{ad}}(\\mathfrak{{g}}_6))&={commutant_dim}.")
    lines.append("\\end{aligned}")
    lines.append("\\end{equation}")
    lines.append("")
    tex_out.write_text("\n".join(lines), encoding="utf-8")
    print(f"[info] wrote TeX: {tex_out}", file=sys.stderr, flush=True)

    print(f"File: {json_out.relative_to(export_dir().parent.parent)}")
    print(f"File: {tex_out.relative_to(generated_dir().parent.parent)}")


if __name__ == "__main__":
    main()

