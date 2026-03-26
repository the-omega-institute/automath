#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit Fibonacci congruence diffusion and inverse-step closed forms.

This audits identities stated in:
  sections/body/zeta_finite_part/xi/subsubsec__xi-fold-congruence-diffusion-hankel-attention.tex

We verify for a small range of m,t:
- p_t on G_m = Z/F_{m+2}Z matches subset-sum distribution and Markov recursion
- Fourier coefficient product formula for characters chi_k(r)=exp(2pi i k r / M)
- Parseval L2 identity for distance to uniform; TV and KL upper bounds
- Inverse-step posterior P(B_t=1 | R_t=r) logistic ratio
- Fourier truncation projection error equals tail energy

Outputs:
- artifacts/export/xi_fib_congruence_diffusion_inverse_audit.json
"""

from __future__ import annotations

import cmath
import json
import math
from dataclasses import dataclass
from typing import Dict, List, Tuple

from common_paths import export_dir


def _fib(n: int) -> int:
    if n <= 0:
        raise ValueError("fib expects n>=1 for this audit")
    a, b = 1, 1
    if n == 1 or n == 2:
        return 1
    for _ in range(3, n + 1):
        a, b = b, a + b
    return b


def _subset_sum_counts_mod(M: int, weights: List[int]) -> List[int]:
    """Counts of subset sums mod M for weights list."""
    c = [0] * M
    c[0] = 1
    for w in weights:
        w %= M
        nxt = c[:]  # choose 0
        for r in range(M):
            nxt[(r + w) % M] += c[r]
        c = nxt
    return c


def _p_from_counts(c: List[int]) -> List[float]:
    total = sum(c)
    return [x / total for x in c]


def _markov_step(p_prev: List[float], shift: int) -> List[float]:
    M = len(p_prev)
    out = [0.0] * M
    for r in range(M):
        out[r] = 0.5 * p_prev[r] + 0.5 * p_prev[(r - shift) % M]
    return out


def _chi(M: int, k: int, r: int) -> complex:
    return cmath.exp(2j * math.pi * (k % M) * (r % M) / M)


def _fourier_coeff(p: List[float], k: int) -> complex:
    M = len(p)
    s = 0j
    for r, pr in enumerate(p):
        s += pr * _chi(M, k, r)
    return s


def _l2_sq(p: List[float], q: List[float]) -> float:
    return sum((a - b) ** 2 for a, b in zip(p, q, strict=True))


def _tv(p: List[float], q: List[float]) -> float:
    return 0.5 * sum(abs(a - b) for a, b in zip(p, q, strict=True))


def _kl(p: List[float], q: List[float]) -> float:
    s = 0.0
    for a, b in zip(p, q, strict=True):
        if a == 0.0:
            continue
        s += a * math.log(a / b)
    return s


def _inverse_posterior(p_prev: List[float], shift: int) -> List[float]:
    M = len(p_prev)
    out = [0.0] * M
    for r in range(M):
        num = p_prev[(r - shift) % M]
        den = p_prev[r] + num
        out[r] = 0.0 if den == 0.0 else num / den
    return out


@dataclass(frozen=True)
class Row:
    m: int
    t: int
    M: int
    ok_distribution: bool
    ok_fourier: bool
    ok_parseval: bool
    ok_bounds: bool
    ok_inverse: bool
    ok_rankk_tail: bool


def main() -> None:
    rows: List[Row] = []

    # Keep this small but nontrivial.
    m_max = 12

    for m in range(1, m_max + 1):
        M = _fib(m + 2)
        u = [1.0 / M] * M

        # p_0
        p_prev = [0.0] * M
        p_prev[0] = 1.0

        for t in range(0, m + 1):
            # subset sum on first t weights F_{j+1}, j=1..t
            weights = [_fib(j + 1) for j in range(1, t + 1)]
            c = _subset_sum_counts_mod(M, weights)
            p_enum = _p_from_counts(c)

            ok_distribution = all(abs(a - b) < 1e-12 for a, b in zip(p_prev, p_enum, strict=True))

            # Fourier product formula: \hat p_t(k) = 2^{-t} prod_{j<=t} (1 + chi_k(F_{j+1}))
            ok_fourier = True
            for k in range(M):
                hat = _fourier_coeff(p_prev, k)
                prod = 1.0 + 0.0j
                for j in range(1, t + 1):
                    prod *= 1.0 + _chi(M, k, _fib(j + 1))
                prod *= (0.5**t)
                if abs(hat - prod) > 1e-10:
                    ok_fourier = False
                    break

            # Parseval: ||p-u||_2^2 = (1/M) sum_{k!=0} |hat p(k)|^2 (characters of Z/MZ)
            hats = [_fourier_coeff(p_prev, k) for k in range(M)]
            l2 = _l2_sq(p_prev, u)
            energy = sum(abs(hats[k]) ** 2 for k in range(1, M)) / M
            ok_parseval = abs(l2 - energy) < 1e-10

            # Bounds: TV <= 0.5*sqrt(M)*||p-u||_2 and KL <= log(1 + sum_{k!=0} |hat|^2)
            tv = _tv(p_prev, u)
            rhs_tv = 0.5 * math.sqrt(M * l2)
            ok_tv = tv <= rhs_tv + 1e-12
            kl = _kl(p_prev, u)
            rhs_kl = math.log(1.0 + sum(abs(hats[k]) ** 2 for k in range(1, M)))
            ok_kl = kl <= rhs_kl + 1e-12
            ok_bounds = ok_tv and ok_kl

            # Inverse-step posterior for t>=1
            ok_inverse = True
            if t >= 1:
                shift = _fib(t + 1)
                # Bayes posterior formula from p_{t-1}
                post = _inverse_posterior(p_prev_prev, shift)  # type: ignore[name-defined]

                # Direct computation: P(B_t=1, R_t=r) = 0.5 * p_{t-1}(r-shift)
                for r in range(M):
                    num = 0.5 * p_prev_prev[(r - shift) % M]  # type: ignore[name-defined]
                    den = p_prev[r]
                    direct = 0.0 if den == 0.0 else num / den
                    if abs(post[r] - direct) > 1e-12:
                        ok_inverse = False
                        break

            # Rank-k Fourier truncation tail energy identity: choose S = {0} U top(k-1) magnitudes.
            # We check this for a couple k values when M is not tiny.
            ok_rankk_tail = True
            if M >= 8:
                mags = [(k, abs(hats[k])) for k in range(M)]
                mags.sort(key=lambda x: x[1], reverse=True)
                for ksize in [3, 5]:
                    if ksize > M:
                        continue
                    S = {mags[i][0] for i in range(ksize)}
                    if 0 not in S:
                        S.remove(next(iter(S)))
                        S.add(0)
                    # projection p^S reconstructed from hats
                    pS: List[complex] = []
                    for r in range(M):
                        s = 0j
                        for kk in S:
                            s += hats[kk] * _chi(M, -kk, r)  # conj(chi_k(r)) = chi_{-k}(r)
                        pS.append(s / M)
                    tail = sum(abs(hats[kk]) ** 2 for kk in range(M) if kk not in S) / M
                    err = sum(abs(complex(p_prev[r]) - pS[r]) ** 2 for r in range(M))
                    if abs(err - tail) > 1e-9:
                        ok_rankk_tail = False
                        break

            rows.append(
                Row(
                    m=m,
                    t=t,
                    M=M,
                    ok_distribution=ok_distribution,
                    ok_fourier=ok_fourier,
                    ok_parseval=ok_parseval,
                    ok_bounds=ok_bounds,
                    ok_inverse=ok_inverse,
                    ok_rankk_tail=ok_rankk_tail,
                )
            )

            # advance Markov recursion (save previous)
            if t < m:
                p_prev_prev = p_prev  # noqa: F841
                shift = _fib(t + 2)  # next step uses F_{(t+1)+1} = F_{t+2}
                p_prev = _markov_step(p_prev, shift)

    assert all(r.ok_distribution for r in rows), "Distribution mismatch"
    assert all(r.ok_fourier for r in rows), "Fourier product mismatch"
    assert all(r.ok_parseval for r in rows), "Parseval mismatch"
    assert all(r.ok_bounds for r in rows), "TV/KL bounds failed"
    assert all(r.ok_inverse for r in rows), "Inverse-step posterior mismatch"
    assert all(r.ok_rankk_tail for r in rows), "Rank-k tail energy mismatch"

    out: Dict[str, object] = {
        "m_max": m_max,
        "results": [
            {
                "m": r.m,
                "t": r.t,
                "M": r.M,
                "ok_distribution": r.ok_distribution,
                "ok_fourier": r.ok_fourier,
                "ok_parseval": r.ok_parseval,
                "ok_bounds": r.ok_bounds,
                "ok_inverse": r.ok_inverse,
                "ok_rankk_tail": r.ok_rankk_tail,
            }
            for r in rows
        ],
    }

    p = export_dir() / "xi_fib_congruence_diffusion_inverse_audit.json"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[ok] wrote {p.relative_to(export_dir().parent)}", flush=True)


if __name__ == "__main__":
    main()

