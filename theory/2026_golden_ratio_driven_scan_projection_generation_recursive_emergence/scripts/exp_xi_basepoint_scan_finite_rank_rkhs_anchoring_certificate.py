#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Numerical audit certificate: finite-rank Pick--Cauchy anchoring identities.

This script provides a reproducible numerical certificate for identities in
subsubsec__xi-basepoint-scan-profile-finite-rank-rkhs-anchoring-part2:
  - full-rank weight gauge invariance of Λ_A(x),
  - det(G_A) factorization (prod w_k) * |det C(A;P)|^2,
  - codim-1 residual kernel rank-one closed form,
  - general codim residual kernel determinant (Plücker/Schur complement).

Outputs:
  - artifacts/export/xi_basepoint_scan_finite_rank_rkhs_anchoring_certificate.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir


def _rng(seed: int) -> np.random.Generator:
    return np.random.default_rng(seed)


def _rand_poles_in_Cminus(g: np.random.Generator, kappa: int) -> np.ndarray:
    # Distinct poles with strictly negative imaginary part.
    re = g.uniform(-2.0, 2.0, size=kappa)
    # Keep poles away from the real axis to reduce ill-conditioning.
    im = -g.uniform(1.0, 3.0, size=kappa)
    p = re + 1j * im
    # enforce distinctness (very high probability already)
    for i in range(kappa):
        for j in range(i):
            if abs(p[i] - p[j]) < 1e-6:
                p[i] += (i + 1) * 1e-3
    return p


def _rand_positive_weights(g: np.random.Generator, kappa: int) -> np.ndarray:
    w = g.uniform(0.2, 3.0, size=kappa)
    return w


def _rand_real_anchors(g: np.random.Generator, n: int) -> np.ndarray:
    a = g.uniform(-2.0, 2.0, size=n)
    # enforce distinctness
    a = np.unique(a)
    while a.size < n:
        a = np.unique(np.concatenate([a, g.uniform(-2.0, 2.0, size=n - a.size)]))
    return a[:n]


def _Pi(z: complex | np.ndarray, poles: np.ndarray) -> complex | np.ndarray:
    out = np.ones_like(z, dtype=np.complex128)
    for pk in poles:
        out = out * (z - pk)
    return out


def _Pi_prime_at_poles(poles: np.ndarray) -> np.ndarray:
    # Π'(p_k)=∏_{j≠k}(p_k-p_j)
    kappa = poles.size
    out = np.ones(kappa, dtype=np.complex128)
    for k in range(kappa):
        prod = 1.0 + 0j
        pk = poles[k]
        for j in range(kappa):
            if j == k:
                continue
            prod *= (pk - poles[j])
        out[k] = prod
    return out


def _yA(z: complex | np.ndarray, anchors: np.ndarray) -> complex | np.ndarray:
    out = np.ones_like(z, dtype=np.complex128)
    for a in anchors:
        out = out * (z - a)
    return out


def _v(x: float, poles: np.ndarray, w: np.ndarray) -> np.ndarray:
    return np.sqrt(w) / (x - poles)


def _K(x: float, y: float, poles: np.ndarray, w: np.ndarray) -> complex:
    # Convention: ⟨u,v⟩ = Σ u_k * conj(v_k) (linear in the first argument),
    # matching the paper's explicit kernel formula.
    vx = _v(x, poles, w)
    vy = _v(y, poles, w)
    return complex(np.dot(vx, np.conj(vy)))


def _gram(anchors: np.ndarray, poles: np.ndarray, w: np.ndarray) -> np.ndarray:
    n = anchors.size
    G = np.empty((n, n), dtype=np.complex128)
    for i in range(n):
        for j in range(n):
            G[i, j] = _K(float(anchors[i]), float(anchors[j]), poles, w)
    return G


def _k_vec(anchors: np.ndarray, x: float, poles: np.ndarray, w: np.ndarray) -> np.ndarray:
    n = anchors.size
    k = np.empty((n,), dtype=np.complex128)
    for i in range(n):
        # k_A(x) = (K(x,a_i))_i, consistent with the paper's convention.
        k[i] = _K(float(x), float(anchors[i]), poles, w)
    return k


def _Cauchy_matrix(anchors: np.ndarray, poles: np.ndarray) -> np.ndarray:
    return 1.0 / (anchors[:, None] - poles[None, :])


def _relative_error(a: complex | float, b: complex | float, eps: float = 1e-15) -> float:
    num = abs(a - b)
    den = max(abs(a), abs(b), eps)
    return float(num / den)


@dataclass(frozen=True)
class CaseResult:
    kappa: int
    n: int
    r: int
    err_det_factorization: float
    err_lambda_weight_invariance: float
    err_codim1_residual_kernel: float
    err_plucker_schur: float
    err_plucker_q_factorization: float


def main() -> None:
    ap = argparse.ArgumentParser(description="Numerical audit: finite-rank Pick--Cauchy anchoring.")
    ap.add_argument("--seed", type=int, default=20260228)
    ap.add_argument("--cases", type=int, default=6)
    ap.add_argument("--json-out", type=str, default=str(export_dir() / "xi_basepoint_scan_finite_rank_rkhs_anchoring_certificate.json"))
    args = ap.parse_args()

    g = _rng(args.seed)
    results: List[CaseResult] = []

    for _ in range(int(args.cases)):
        kappa = int(g.integers(3, 7))
        # pick n up to full rank (include n=kappa cases)
        n = int(g.integers(max(1, kappa - 3), kappa + 1))
        r = kappa - n

        # Generate a numerically stable configuration (deterministic under the seed).
        stable_tries = 0
        while True:
            poles = _rand_poles_in_Cminus(g, kappa)
            w1 = _rand_positive_weights(g, kappa)
            w2 = _rand_positive_weights(g, kappa)  # independent weights for gauge test
            anchors = _rand_real_anchors(g, n)

            min_sep = float(np.min(np.abs(anchors[:, None] - poles[None, :])))
            if min_sep <= 0.4:
                stable_tries += 1
                if stable_tries >= 200:
                    break
                continue

            G_A = _gram(anchors, poles, w1)
            cond = float(np.linalg.cond(G_A))
            if not np.isfinite(cond) or cond > 1e6:
                stable_tries += 1
                if stable_tries >= 200:
                    break
                continue
            break
        # pick test x,y not in anchors
        x = float(g.uniform(-2.5, 2.5))
        y = float(g.uniform(-2.5, 2.5))
        if np.min(np.abs(anchors - x)) < 1e-4:
            x += 0.123
        if np.min(np.abs(anchors - y)) < 1e-4:
            y -= 0.137

        # det factorization in full rank only
        err_det = 0.0
        err_lam = 0.0
        if n == kappa:
            C = _Cauchy_matrix(anchors, poles)
            G = _gram(anchors, poles, w1)
            detG = np.linalg.det(G)
            rhs = np.prod(w1) * abs(np.linalg.det(C)) ** 2
            err_det = _relative_error(detG, rhs)

            # Λ_A(x) in the paper is defined via k_A(x)=(K(a_i,x))_i.
            kvec = np.conj(_k_vec(anchors, x, poles, w1))
            lam1 = np.linalg.solve(G, kvec)

            # change weights, recompute; Λ should be invariant
            G2 = _gram(anchors, poles, w2)
            kvec2 = np.conj(_k_vec(anchors, x, poles, w2))
            lam2 = np.linalg.solve(G2, kvec2)
            err_lam = float(np.linalg.norm(lam1 - lam2) / max(np.linalg.norm(lam1), np.linalg.norm(lam2), 1e-15))

        # codim-1 residual kernel closed form
        err_codim1 = 0.0
        if n == kappa - 1:
            G = _gram(anchors, poles, w1)
            kx = _k_vec(anchors, x, poles, w1)
            # K(A,y) has entries K(a_i,y)=conj(K(y,a_i)).
            Ky = np.conj(_k_vec(anchors, y, poles, w1))
            sol = np.linalg.solve(G, Ky)
            # Residual kernel: R(x,y)=K(x,y)-K(x,A)G_A^{-1}K(A,y).
            Rxy = _K(x, y, poles, w1) - (kx @ sol)

            Pi_x = _Pi(x, poles)
            Pi_y = _Pi(y, poles)
            Pi_prime = _Pi_prime_at_poles(poles)
            yAx = _yA(x, anchors)
            yAy = _yA(y, anchors)
            denom = 0.0 + 0j
            for k in range(kappa):
                denom += abs(_yA(poles[k], anchors)) ** 2 / (w1[k] * abs(Pi_prime[k]) ** 2)
            rhs = (yAx * np.conj(yAy) / (Pi_x * np.conj(Pi_y))) / denom
            err_codim1 = _relative_error(Rxy, rhs)

        # general Plücker/Schur complement certificate
        err_plucker = 0.0
        err_plucker_q = 0.0
        if r >= 1:
            # choose X of size r away from anchors
            X = []
            while len(X) < r:
                t = float(g.uniform(-2.5, 2.5))
                if np.min(np.abs(anchors - t)) < 1e-3:
                    continue
                if any(abs(t - u) < 1e-3 for u in X):
                    continue
                X.append(t)
            X = np.array(X, dtype=float)

            G_A = _gram(anchors, poles, w1)
            detA = np.linalg.det(G_A)

            AX = np.concatenate([anchors, X])
            G_AX = _gram(AX, poles, w1)
            detAX = np.linalg.det(G_AX)

            # Schur complement residual matrix
            R = np.empty((r, r), dtype=np.complex128)
            for i in range(r):
                kxi = _k_vec(anchors, float(X[i]), poles, w1)
                for j in range(r):
                    kxj = _k_vec(anchors, float(X[j]), poles, w1)
                    KAxj = np.conj(kxj)  # entries K(a_i,x_j)
                    sol = np.linalg.solve(G_A, KAxj)
                    R[i, j] = _K(float(X[i]), float(X[j]), poles, w1) - (kxi @ sol)
            rhs_det = detA * np.linalg.det(R)
            err_plucker = _relative_error(detAX, rhs_det)

            # q-factorization (orthonormalize monomials w.r.t. discrete residue inner product)
            Pi_prime = _Pi_prime_at_poles(poles)
            yAp = _yA(poles, anchors)
            wt = (abs(yAp) ** 2) / (w1 * (abs(Pi_prime) ** 2))
            # Gram for monomials z^0..z^{r-1}
            M = np.empty((r, r), dtype=np.complex128)
            for i in range(r):
                for j in range(r):
                    M[i, j] = np.sum((poles ** i) * np.conj(poles ** j) * wt)
            # Orthonormal basis: coefficients matrix B such that q(z) = sum_i B[i,j] z^i and B^* M B = I
            # Use Cholesky on M (Hermitian posdef)
            L = np.linalg.cholesky(M)
            B = np.linalg.inv(L).conj().T  # then B^* M B = I
            # Evaluate q_j at X_i: Q = Vmon(X) @ B
            Vmon = np.vstack([X ** i for i in range(r)]).T.astype(np.complex128)  # (r x r)
            Q = Vmon @ B
            # Factorization det(R) = prod |yA/Pi|^2 * |det Q|^2
            diag = _yA(X, anchors) / _Pi(X, poles)
            Dabs2 = float(np.prod(np.abs(diag) ** 2))
            rhs_detR = Dabs2 * abs(np.linalg.det(Q)) ** 2
            err_plucker_q = _relative_error(np.linalg.det(R), rhs_detR)

        results.append(
            CaseResult(
                kappa=kappa,
                n=n,
                r=r,
                err_det_factorization=float(err_det),
                err_lambda_weight_invariance=float(err_lam),
                err_codim1_residual_kernel=float(err_codim1),
                err_plucker_schur=float(err_plucker),
                err_plucker_q_factorization=float(err_plucker_q),
            )
        )

    payload: Dict[str, object] = {
        "meta": {"script": Path(__file__).name, "seed": int(args.seed), "cases": int(args.cases), "numpy": np.__version__},
        "results": [asdict(r) for r in results],
        "max_errors": {
            "det_factorization": max(r.err_det_factorization for r in results),
            "lambda_weight_invariance": max(r.err_lambda_weight_invariance for r in results),
            "codim1_residual_kernel": max(r.err_codim1_residual_kernel for r in results),
            "plucker_schur": max(r.err_plucker_schur for r in results),
            "plucker_q_factorization": max(r.err_plucker_q_factorization for r in results),
        },
    }

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[xi-basepoint-scan-finite-rank-rkhs-anchoring] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

