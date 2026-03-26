#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit FRACTRAN compilation of Fold normalization.

Verifies (finite windows):
  1) FRACTRAN program Π_L (L=m+2) normalizes prime-register encodings to the
     Zeckendorf normal form (truncated to m bits).
  2) All-ones input reduction length T(m) = floor(m^2/4) for the Π_{m+1} program.

Output:
  - artifacts/export/fold_fractran_fold_compiler_audit.json
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _first_n_primes(n: int) -> List[int]:
    out: List[int] = []
    p = 2
    while len(out) < n:
        if sp.isprime(p):
            out.append(p)
        p += 1
    return out


def _fibs(n: int) -> List[int]:
    """Return Fibonacci numbers F_0..F_n with F_0=0,F_1=1."""
    f = [0, 1]
    for _ in range(2, n + 1):
        f.append(f[-1] + f[-2])
    return f


def _zeckendorf_digits(n: int, max_k: int) -> List[int]:
    """Return digits z_1..z_max_k for weights F_{k+1}."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    if n == 0:
        return [0] * max_k
    # Precompute weights w_k = F_{k+1}.
    f = _fibs(max_k + 3)
    w = [f[k + 1] for k in range(1, max_k + 1)]  # index 0 corresponds to k=1
    z = [0] * max_k
    k = max_k
    rem = n
    while rem > 0 and k >= 1:
        if w[k - 1] <= rem:
            z[k - 1] = 1
            rem -= w[k - 1]
            k -= 2  # skip adjacent weight
        else:
            k -= 1
    if rem != 0:
        raise RuntimeError("zeckendorf greedy failed to terminate")
    # Sanity: no adjacent 1.
    for i in range(max_k - 1):
        if z[i] == 1 and z[i + 1] == 1:
            raise RuntimeError("adjacent ones in zeckendorf digits")
    return z


def _fold_digits(omega: Sequence[int], m: int) -> List[int]:
    # N(omega) = sum_{k=1}^m omega_k F_{k+1}
    f = _fibs(m + 4)
    n = sum(int(omega[k - 1]) * f[k + 1] for k in range(1, m + 1))
    z = _zeckendorf_digits(n, max_k=m + 2)
    return z[:m]


def _fractran_program_steps(L: int) -> List[Tuple[str, int]]:
    """Return ordered rule list tags (kind, k).

    Kinds:
      - "dedup1": k=1
      - "dedup2": k=2
      - "dedupk": k>=3
      - "adj":    k>=1
    """
    steps: List[Tuple[str, int]] = [("dedup1", 1), ("dedup2", 2)]
    for k in range(3, L):  # k=3..L-1
        steps.append(("dedupk", k))
    for k in range(1, L - 1):  # k=1..L-2
        steps.append(("adj", k))
    return steps


def _fractran_run_exponents(a0: Sequence[int], L: int) -> Tuple[List[int], int]:
    """Run Π_L on exponent vector a_1..a_L (nonnegative integers)."""
    a = list(map(int, a0))
    if len(a) != L:
        raise ValueError("length mismatch")
    steps = _fractran_program_steps(L)
    t = 0
    while True:
        applied = False
        for kind, k in steps:
            idx = k - 1
            if kind == "dedup1":
                if a[0] >= 2:
                    a[0] -= 2
                    a[1] += 1
                    applied = True
            elif kind == "dedup2":
                if a[1] >= 2:
                    a[1] -= 2
                    a[0] += 1
                    a[2] += 1
                    applied = True
            elif kind == "dedupk":
                # k>=3
                if a[idx] >= 2:
                    a[idx] -= 2
                    a[idx - 2] += 1
                    a[idx + 1] += 1
                    applied = True
            elif kind == "adj":
                # requires k,k+1 -> k+2, and k+2 <= L
                if a[idx] >= 1 and a[idx + 1] >= 1:
                    a[idx] -= 1
                    a[idx + 1] -= 1
                    a[idx + 2] += 1
                    applied = True
            else:
                raise RuntimeError("unknown kind")
            if applied:
                t += 1
                break
        if not applied:
            return a, t


def _all_ones_steps(m: int) -> int:
    """Run Π_{m+1} on initial (1..1,0) and return steps."""
    L = m + 1
    a0 = [1] * m + [0]
    _, t = _fractran_run_exponents(a0, L=L)
    return t


@dataclass(frozen=True)
class Payload:
    compiler_m_max: int
    compiler_all_ok: bool
    compiler_first_failure: Optional[Dict[str, object]]
    compiler_checked: int
    compiler_max_steps_observed: int
    all_ones_m_max: int
    all_ones_all_ok: bool
    all_ones_first_failure: Optional[Dict[str, object]]
    all_ones_max_steps_observed: int
    elapsed_s: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit FRACTRAN compilation of Fold normalization.")
    parser.add_argument("--m-max", type=int, default=12, help="Max m for exhaustive compiler check (2^m states).")
    parser.add_argument("--m-ones-max", type=int, default=60, help="Max m for all-ones step law check.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    args = parser.parse_args()

    t0 = time.time()
    m_max = int(args.m_max)
    m_ones_max = int(args.m_ones_max)

    compiler_checked = 0
    compiler_first_failure: Optional[Dict[str, object]] = None
    compiler_max_steps = 0

    for m in range(1, m_max + 1):
        L = m + 2
        for mask in range(1 << m):
            omega = [(mask >> (k - 1)) & 1 for k in range(1, m + 1)]
            # FRACTRAN on exponent vector (omega,0,0)
            a0 = omega + [0, 0]
            a_fin, steps = _fractran_run_exponents(a0, L=L)
            compiler_max_steps = max(compiler_max_steps, steps)
            got = a_fin[:m]
            want = _fold_digits(omega, m=m)
            compiler_checked += 1
            if got != want:
                compiler_first_failure = {
                    "m": m,
                    "omega_bits": omega,
                    "mask": mask,
                    "fractran_output_prefix": got,
                    "fold_prefix": want,
                    "steps": steps,
                    "L": L,
                }
                break
        if compiler_first_failure is not None:
            break

    all_ones_first_failure: Optional[Dict[str, object]] = None
    all_ones_max_steps = 0
    for m in range(1, m_ones_max + 1):
        t_steps = _all_ones_steps(m)
        all_ones_max_steps = max(all_ones_max_steps, t_steps)
        target = (m * m) // 4
        if t_steps != target:
            all_ones_first_failure = {"m": m, "steps": t_steps, "target": target}
            break

    payload = Payload(
        compiler_m_max=m_max,
        compiler_all_ok=(compiler_first_failure is None),
        compiler_first_failure=compiler_first_failure,
        compiler_checked=compiler_checked,
        compiler_max_steps_observed=compiler_max_steps,
        all_ones_m_max=m_ones_max,
        all_ones_all_ok=(all_ones_first_failure is None),
        all_ones_first_failure=all_ones_first_failure,
        all_ones_max_steps_observed=all_ones_max_steps,
        elapsed_s=float(time.time() - t0),
    )

    if not args.no_output:
        out = export_dir() / "fold_fractran_fold_compiler_audit.json"
        _write_json(out, asdict(payload))
        print(f"[fold-fractran-audit] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

