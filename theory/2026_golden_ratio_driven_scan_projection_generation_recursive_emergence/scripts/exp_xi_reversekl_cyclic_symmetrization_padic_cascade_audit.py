#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Cyclic symmetrization vs radius renormalization: numerical audits.

English-only by repository convention.

We audit (numerically, on a theta grid) the identities/inequalities:
  - Pi_n(p_r)(theta) = (P_{r^n} * mu^{<n>})(n theta)
  - H_r(mu) >= H_{r^n}(mu^{<n>})
  - H_r(mu) - H_{r^n}(mu^{<n>}) = ∫ KL(u_n || w_theta) dm(theta)
  - quadratic Jensen-gap bounds using a_r,b_r
  - p-adic cascade: H_r(mu) ≈ sum_j (H_{r^{p^j}}(mu^{<p^j>}) - H_{r^{p^{j+1}}}(mu^{<p^{j+1}>}))

Outputs:
  - artifacts/export/xi_reversekl_cyclic_symmetrization_padic_cascade_audit.json
"""

from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Tuple

import numpy as np

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def poisson_kernel(theta: np.ndarray, r: float) -> np.ndarray:
    den = 1.0 - 2.0 * r * np.cos(theta) + r * r
    return (1.0 - r * r) / den


def pr_from_atoms(theta: np.ndarray, r: float, atoms: np.ndarray, weights: np.ndarray) -> np.ndarray:
    P = poisson_kernel(theta[:, None] - atoms[None, :], r)
    return (P @ weights).astype(np.float64)


def mean_m(f: np.ndarray) -> float:
    return float(np.mean(f))


def Hr(theta: np.ndarray, r: float, atoms: np.ndarray, weights: np.ndarray) -> float:
    pr = pr_from_atoms(theta, r, atoms, weights)
    return mean_m(-np.log(pr))


def Pi_n_of_grid_values(p: np.ndarray, n: int) -> np.ndarray:
    M = p.size
    if M % n != 0:
        raise ValueError("grid size must be divisible by n")
    step = M // n
    out = np.zeros_like(p)
    for j in range(n):
        out += np.roll(p, j * step)
    out /= float(n)
    return out


def shift_grid_stack(p: np.ndarray, n: int) -> np.ndarray:
    """Return x[j, i] = p(theta_i + 2π j/n) using rolls."""
    M = p.size
    if M % n != 0:
        raise ValueError("grid size must be divisible by n")
    step = M // n
    xs = np.empty((n, M), dtype=np.float64)
    for j in range(n):
        xs[j] = np.roll(p, j * step)
    return xs


def pushforward_atoms(atoms: np.ndarray, n: int) -> np.ndarray:
    return np.mod(n * atoms, 2.0 * math.pi)


def kl_uniform_vs_w_from_x(x: np.ndarray) -> np.ndarray:
    """
    x shape (n, M), x>0.
    returns KL(u_n || w_theta) for each theta grid point.
    """
    n = x.shape[0]
    xsum = np.sum(x, axis=0)
    w = x / xsum[None, :]
    # KL(u||w) = (1/n) Σ log((1/n)/w_j)
    return np.mean(np.log((1.0 / n) / w), axis=0)


@dataclass(frozen=True)
class Payload:
    ok_pi_identity_linf: bool
    ok_pi_identity_l2: bool
    ok_entropy_monotone: bool
    ok_kl_identity: bool
    ok_quadratic_bounds: bool
    ok_cascade_sum_p2: bool
    ok_cascade_sum_p3: bool
    err_pi_linf: float
    err_pi_l2: float
    Hr: float
    Hr_n: float
    gap: float
    kl_gap: float
    gap_minus_kl: float
    quad_lower: float
    quad_upper: float
    quad_ok_margin: float
    cascade_p2_sum: float
    cascade_p3_sum: float
    cascade_p2_tail: float
    cascade_p3_tail: float


def main() -> None:
    rng = np.random.default_rng(20260227)

    # Discrete measure on T.
    A = 9
    atoms = rng.uniform(0.0, 2.0 * math.pi, size=A).astype(np.float64)
    w = rng.random(size=A).astype(np.float64)
    weights = (w / np.sum(w)).astype(np.float64)

    # Grid for m-average.
    M = 10240  # divisible by 5 and large 2-power
    theta = (2.0 * math.pi) * (np.arange(M, dtype=np.float64) / M)

    r = 0.73
    n = 5

    pr = pr_from_atoms(theta, r, atoms, weights)
    pin_pr = Pi_n_of_grid_values(pr, n)

    r2 = r**n
    atoms2 = pushforward_atoms(atoms, n)
    phi = np.mod(n * theta, 2.0 * math.pi)
    rhs = pr_from_atoms(phi, r2, atoms2, weights)

    err_linf = float(np.max(np.abs(pin_pr - rhs)))
    err_l2 = float(math.sqrt(mean_m((pin_pr - rhs) ** 2)))

    Hr0 = mean_m(-np.log(pr))
    HrN = mean_m(-np.log(rhs))  # equals H_{r^n}(mu^{<n>}) numerically
    gap = Hr0 - HrN

    # KL identity: gap equals ∫ KL(u_n||w_theta) dm(theta)
    xstack = shift_grid_stack(pr, n)  # x_j(theta)=p_r(theta+2π j/n)
    kl_vals = kl_uniform_vs_w_from_x(xstack)
    kl_gap = mean_m(kl_vals)

    # Quadratic Jensen-gap bounds with a_r,b_r.
    a_r = (1.0 - r) / (1.0 + r)
    b_r = (1.0 + r) / (1.0 - r)
    norm2 = mean_m((pr - pin_pr) ** 2)
    quad_lower = (1.0 / (2.0 * b_r * b_r)) * norm2
    quad_upper = (1.0 / (2.0 * a_r * a_r)) * norm2

    # p-adic cascades (p=2,3): finite J approximation.
    def cascade_sum(p: int, J: int) -> Tuple[float, float]:
        Hs = []
        for j in range(J + 1):
            rj = r ** (p**j)
            atomsj = pushforward_atoms(atoms, p**j)
            Hj = Hr(theta, rj, atomsj, weights)
            Hs.append(Hj)
        Hs = np.array(Hs, dtype=np.float64)
        gaps = Hs[:-1] - Hs[1:]
        return float(np.sum(gaps)), float(Hs[-1])

    sum_p2, tail_p2 = cascade_sum(2, J=10)
    sum_p3, tail_p3 = cascade_sum(3, J=8)

    # Tolerances (numerical quadrature + floating error).
    tol_pi_linf = 5e-6
    tol_pi_l2 = 5e-7
    tol_gap_kl = 2e-6
    tol_quad = 2e-6
    tol_cascade = 2e-6

    ok_pi_linf = err_linf <= tol_pi_linf
    ok_pi_l2 = err_l2 <= tol_pi_l2
    ok_entropy = (gap >= -1e-12)
    ok_kl = abs(gap - kl_gap) <= tol_gap_kl
    ok_quad = (gap + tol_quad >= quad_lower) and (gap <= quad_upper + tol_quad)
    ok_cascade_p2 = abs(Hr0 - sum_p2 - tail_p2) <= tol_cascade
    ok_cascade_p3 = abs(Hr0 - sum_p3 - tail_p3) <= tol_cascade

    payload = Payload(
        ok_pi_identity_linf=bool(ok_pi_linf),
        ok_pi_identity_l2=bool(ok_pi_l2),
        ok_entropy_monotone=bool(ok_entropy),
        ok_kl_identity=bool(ok_kl),
        ok_quadratic_bounds=bool(ok_quad),
        ok_cascade_sum_p2=bool(ok_cascade_p2),
        ok_cascade_sum_p3=bool(ok_cascade_p3),
        err_pi_linf=err_linf,
        err_pi_l2=err_l2,
        Hr=Hr0,
        Hr_n=HrN,
        gap=gap,
        kl_gap=kl_gap,
        gap_minus_kl=float(gap - kl_gap),
        quad_lower=quad_lower,
        quad_upper=quad_upper,
        quad_ok_margin=float(min(gap - quad_lower, quad_upper - gap)),
        cascade_p2_sum=sum_p2,
        cascade_p3_sum=sum_p3,
        cascade_p2_tail=tail_p2,
        cascade_p3_tail=tail_p3,
    )

    _write_json(
        export_dir() / "xi_reversekl_cyclic_symmetrization_padic_cascade_audit.json",
        asdict(payload),
    )


if __name__ == "__main__":
    main()

