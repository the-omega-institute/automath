#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Numerical audit for Cayley--Poisson multipole identities in the Poisson--Cauchy model.

We verify, for discrete input measures nu on R:
  - u(theta) = E[(1-|W|^2)/|e^{i theta}-W|^2] and its Fourier coefficients m_k = E[W^k].
  - chi^2(h_t|g_t) = 2 * sum_{k>=1} |m_k(t)|^2.
  - L2 truncation error equals the tail energy 2 * sum_{k>N} |m_k|^2.
  - Moment chain: t d/dt m_k = -k(m_k - m_{k+1}).
  - Dissipation: d/dt (t chi^2) = -2 * sum_{k>=1} k |m_k - m_{k+1}|^2.
  - Möbius covariance: W_{s t} = Phi_s(W_t), and Koenigs linearization.

Outputs:
  - artifacts/export/xi_poisson_cauchy_cayley_multipole_audit.json
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _phi_s(u: np.ndarray, s: float) -> np.ndarray:
    return u / (s - (s - 1.0) * u)


def _koenigs(u: np.ndarray) -> np.ndarray:
    return u / (1.0 - u)


def _discrete_case(gammas: np.ndarray, weights: np.ndarray) -> Tuple[np.ndarray, np.ndarray, float]:
    w = np.asarray(weights, dtype=np.float64)
    w = w / float(np.sum(w))
    g = np.asarray(gammas, dtype=np.float64)
    mu = float(np.sum(w * g))
    a = g - mu
    return g, w, mu


def _W(a: np.ndarray, t: float) -> np.ndarray:
    return a / (a + 2j * t)


def _W_prime(a: np.ndarray, t: float) -> np.ndarray:
    # d/dt [ a/(a+2 i t) ] = -2 i a / (a+2 i t)^2
    return (-2j * a) / (a + 2j * t) ** 2


def _mk(Wt: np.ndarray, w: np.ndarray, kmax: int) -> np.ndarray:
    m = np.empty(kmax + 2, dtype=np.complex128)  # include kmax+1 for chain RHS
    pow_ = Wt.copy()
    for k in range(1, kmax + 2):
        m[k] = np.sum(w * pow_)
        pow_ = pow_ * Wt
    m[0] = 1.0 + 0j
    return m


def _u_theta(Wt: np.ndarray, w: np.ndarray, theta: np.ndarray) -> np.ndarray:
    z = np.exp(1j * theta)
    # u(theta) = E[(1-|W|^2)/|z-W|^2]
    u = np.zeros_like(theta, dtype=np.float64)
    for Wi, wi in zip(Wt, w):
        num = 1.0 - (Wi.real * Wi.real + Wi.imag * Wi.imag)
        den = np.abs(z - Wi) ** 2
        u += float(wi) * (num / den)
    return u


def _uN_theta(m: np.ndarray, theta: np.ndarray, N: int) -> np.ndarray:
    # u_N(theta) = 1 + sum_{k=1..N} (m_k e^{-ikθ} + conj(m_k) e^{ikθ})
    k = np.arange(1, N + 1, dtype=np.float64)
    e_neg = np.exp(-1j * np.outer(theta, k))
    s = e_neg @ m[1 : N + 1]
    return 1.0 + 2.0 * np.real(s)


def _mean_square(f: np.ndarray) -> float:
    return float(np.mean(np.square(f)))


def _tail_bound_mk_sq(r: float, k0: int) -> float:
    # sum_{k>=k0} r^{2k} = r^{2k0} / (1-r^2)
    rr2 = r * r
    if rr2 >= 1.0:
        return float("inf")
    return (r ** (2 * k0)) / (1.0 - rr2)


def _tail_bound_k_diff_sq(r: float, k0: int) -> float:
    # crude bound: |m_k - m_{k+1}| <= |m_k|+|m_{k+1}| <= r^k + r^{k+1} = (1+r) r^k
    # sum_{k>=k0} k |m_k-m_{k+1}|^2 <= (1+r)^2 * sum_{k>=k0} k r^{2k}
    rr2 = r * r
    if rr2 >= 1.0:
        return float("inf")
    # sum_{k>=k0} k q^k = (k0 q^k0 - (k0-1) q^{k0+1}) / (1-q)^2, for |q|<1
    q = rr2
    num = k0 * (q**k0) - (k0 - 1) * (q ** (k0 + 1))
    denom = (1.0 - q) ** 2
    return ((1.0 + r) ** 2) * (num / denom)


@dataclass(frozen=True)
class AuditRow:
    name: str
    t: float
    theta_M: int
    kmax: int
    N: int
    r_max_absW: float
    chi2_theta: float
    chi2_mk_partial: float
    chi2_mk_tail_upper: float
    chi2_abs_err: float
    trunc_err_theta: float
    trunc_tail_energy_partial: float
    trunc_tail_upper: float
    trunc_abs_err: float
    moment_chain_max_abs_err_k20: float
    dissipation_lhs: float
    dissipation_rhs_partial: float
    dissipation_rhs_tail_upper: float
    dissipation_abs_err: float
    mobius_max_abs_err: float
    koenigs_max_abs_err: float


def _audit_one(name: str, gammas: np.ndarray, weights: np.ndarray, *, t: float, s: float) -> AuditRow:
    _, w, mu = _discrete_case(gammas, weights)
    a = gammas - mu
    Wt = _W(a, t)
    r = float(np.max(np.abs(Wt)))

    M = 1 << 14  # 16384 points (periodic trapezoid is spectrally accurate for smooth periodic integrands)
    theta = (2.0 * np.pi) * (np.arange(M, dtype=np.float64) / float(M))
    u = _u_theta(Wt, w, theta)

    chi2_theta = _mean_square(u - 1.0)

    kmax = 600
    m = _mk(Wt, w, kmax)
    chi2_partial = 2.0 * float(np.sum(np.abs(m[1 : kmax + 1]) ** 2))
    chi2_tail = 2.0 * _tail_bound_mk_sq(r, kmax + 1)
    chi2_err = float(abs(chi2_theta - chi2_partial))

    N = 80
    uN = _uN_theta(m, theta, N)
    trunc_err_theta = _mean_square(u - uN)
    trunc_tail_partial = 2.0 * float(np.sum(np.abs(m[N + 1 : kmax + 1]) ** 2))
    trunc_tail_upper = 2.0 * _tail_bound_mk_sq(r, kmax + 1)
    trunc_err = float(abs(trunc_err_theta - trunc_tail_partial))

    # Moment chain check: compare direct derivative vs -k/t (m_k - m_{k+1})
    Wp = _W_prime(a, t)
    chain_max = 0.0
    for k in range(1, 21):
        mk_direct = np.sum(w * (k * (Wt ** (k - 1)) * Wp))
        mk_chain = (-(k / t)) * (m[k] - m[k + 1])
        chain_max = max(chain_max, float(abs(mk_direct - mk_chain)))

    # Dissipation identity check using truncated sums and tail bound.
    # LHS: d/dt (t chi2) computed from moment chain with truncation.
    mk_prime = np.empty(kmax + 1, dtype=np.complex128)
    for k in range(1, kmax + 1):
        mk_prime[k] = (-(k / t)) * (m[k] - m[k + 1])
    chi2_prime_partial = 4.0 * float(np.sum(np.real(mk_prime[1 : kmax + 1] * np.conj(m[1 : kmax + 1]))))
    diss_lhs = float(chi2_partial + t * chi2_prime_partial)

    diff = m[1 : kmax + 1] - m[2 : kmax + 2]
    diss_rhs_partial = -2.0 * float(np.sum((np.arange(1, kmax + 1, dtype=np.float64)) * (np.abs(diff) ** 2)))
    diss_rhs_tail = -2.0 * _tail_bound_k_diff_sq(r, kmax + 1)
    diss_err = float(abs(diss_lhs - diss_rhs_partial))

    # Möbius covariance and Koenigs linearization.
    st = s * t
    Wst = _W(a, st)
    Phi = _phi_s(Wt, s)
    mobius_max = float(np.max(np.abs(Wst - Phi)))
    koenigs_max = float(np.max(np.abs(_koenigs(Phi) - (_koenigs(Wt) / s))))

    return AuditRow(
        name=name,
        t=float(t),
        theta_M=int(M),
        kmax=int(kmax),
        N=int(N),
        r_max_absW=float(r),
        chi2_theta=float(chi2_theta),
        chi2_mk_partial=float(chi2_partial),
        chi2_mk_tail_upper=float(chi2_tail),
        chi2_abs_err=float(chi2_err),
        trunc_err_theta=float(trunc_err_theta),
        trunc_tail_energy_partial=float(trunc_tail_partial),
        trunc_tail_upper=float(trunc_tail_upper),
        trunc_abs_err=float(trunc_err),
        moment_chain_max_abs_err_k20=float(chain_max),
        dissipation_lhs=float(diss_lhs),
        dissipation_rhs_partial=float(diss_rhs_partial),
        dissipation_rhs_tail_upper=float(diss_rhs_tail),
        dissipation_abs_err=float(diss_err),
        mobius_max_abs_err=float(mobius_max),
        koenigs_max_abs_err=float(koenigs_max),
    )


def main() -> None:
    # Two cases: a nontrivial discrete mixture and the degenerate delta at the mean.
    cases = [
        (
            "mixture3",
            np.array([-1.7, 0.4, 2.3], dtype=np.float64),
            np.array([0.25, 0.35, 0.40], dtype=np.float64),
        ),
        (
            "delta_mean",
            np.array([1.0], dtype=np.float64),
            np.array([1.0], dtype=np.float64),
        ),
    ]
    t_list = [0.35, 0.9, 2.4]
    s = 3.7

    rows: List[Dict[str, object]] = []
    for name, g, w in cases:
        for t in t_list:
            row = _audit_one(name, g, w, t=t, s=s)
            rows.append(asdict(row))

    payload: Dict[str, object] = {
        "ok": True,
        "s_mobius": float(s),
        "rows": rows,
        "notes": {
            "chi2_tail_bound": "2 * sum_{k>=k0} |m_k|^2 <= 2 * r^{2 k0} / (1-r^2), r=max|W|",
            "dissipation_tail_bound": "crude geometric bound on sum_{k>=k0} k|m_k-m_{k+1}|^2 using |m_k|<=r^k",
        },
    }

    out_json = export_dir() / "xi_poisson_cauchy_cayley_multipole_audit.json"
    _write_json(out_json, payload)
    print("[xi-poisson-cauchy-cayley-multipole-audit] ok")


if __name__ == "__main__":
    main()

