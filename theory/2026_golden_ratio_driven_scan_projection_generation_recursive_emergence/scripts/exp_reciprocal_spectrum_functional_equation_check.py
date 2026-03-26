#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Check the reciprocal-spectrum closure that implies an s <-> 1-s functional equation.

We test, for a given finite matrix M with Perron root lambda = rho(M) > 0:

  (Reciprocal closure)  mu in Spec(M)\\{0\\}  ==>  lambda/mu in Spec(M)\\{0\\}  (same multiplicity)

This is exactly the eigenvalue version of the z-variable involution
  z  <->  1/(lambda z)
for Delta(z) = det(I - z M), under the Dirichlet coordinate z = lambda^{-s}.

Outputs (default):
- artifacts/export/reciprocal_spectrum_functional_equation_check.json
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import numpy as np

from common_paths import export_dir
from common_phi_fold import Progress


@dataclass(frozen=True)
class PairingStats:
    lambda_pf: float
    nonzero_count: int
    matched_count: int
    unmatched: List[Dict[str, object]]
    max_abs_err: float
    max_rel_err: float


def _as_json_complex(z: complex) -> Dict[str, float]:
    return {"re": float(np.real(z)), "im": float(np.imag(z))}


def perron_root_from_eigs(eigs: np.ndarray) -> float:
    return float(np.max(np.abs(eigs)))


def reciprocal_pairing_check(
    eigs: np.ndarray,
    lambda_pf: float,
    *,
    zero_tol: float,
    abs_tol: float,
    rel_tol: float,
    prog: Optional[Progress] = None,
) -> PairingStats:
    # Keep only nonzero eigenvalues (zeros contribute no z-roots and are not invertible under mu -> lambda/mu).
    nonzero = [complex(x) for x in eigs if abs(complex(x)) > zero_tol]
    n = len(nonzero)
    used = [False] * n

    matched = 0
    unmatched_rows: List[Dict[str, object]] = []
    max_abs_err = 0.0
    max_rel_err = 0.0

    for i, mu in enumerate(nonzero):
        if used[i]:
            continue

        # Fixed points under mu -> lambda/mu satisfy mu^2 = lambda.
        # In a multiset closure check, such eigenvalues are allowed to map to themselves.
        fixed_err = abs(mu * mu - complex(lambda_pf))
        fixed_rel = fixed_err / max(1.0, abs(lambda_pf))
        if (fixed_err <= abs_tol) or (fixed_rel <= rel_tol):
            used[i] = True
            matched += 1
            if prog:
                prog.tick(f"pair {matched}/{n} (fixed)")
            continue

        used[i] = True
        target = complex(lambda_pf) / mu

        best_j = None
        best_err = float("inf")
        for j in range(n):
            if used[j]:
                continue
            err = abs(nonzero[j] - target)
            if err < best_err:
                best_err = err
                best_j = j

        if best_j is None:
            unmatched_rows.append({"mu": _as_json_complex(mu), "target": _as_json_complex(target), "reason": "no candidate"})
            if prog:
                prog.tick(f"pair {matched}/{n} (no candidate)")
            continue

        denom = max(1.0, abs(target))
        rel = best_err / denom
        ok = (best_err <= abs_tol) or (rel <= rel_tol)

        max_abs_err = max(max_abs_err, float(best_err))
        max_rel_err = max(max_rel_err, float(rel))

        if ok:
            used[best_j] = True
            matched += 2 if best_j != i else 1
        else:
            unmatched_rows.append(
                {
                    "mu": _as_json_complex(mu),
                    "target": _as_json_complex(target),
                    "closest": _as_json_complex(nonzero[best_j]),
                    "abs_err": float(best_err),
                    "rel_err": float(rel),
                }
            )

        if prog:
            prog.tick(f"pair {matched}/{n}")

    return PairingStats(
        lambda_pf=float(lambda_pf),
        nonzero_count=n,
        matched_count=matched,
        unmatched=unmatched_rows,
        max_abs_err=float(max_abs_err),
        max_rel_err=float(max_rel_err),
    )


def filtered_nonzero_eigs(eigs: np.ndarray, *, zero_tol: float) -> List[complex]:
    out = [complex(x) for x in eigs if abs(complex(x)) > zero_tol]
    out.sort(key=lambda z: (-abs(z), z.real, z.imag))
    return out


def poly_lambda_reciprocity_check_integer_coeffs(
    coeffs: List[int],
    lambda_pf: int,
) -> Dict[str, object]:
    """Exact coefficient-level check for:

    Delta(z) := sum_{k=0}^r c_k z^k  with integer c_k, c_0 = 1.

    We test whether there exists a nonzero constant C such that
        z^r Delta(1/(lambda z)) = C * Delta(z)

    Over Q, this is equivalent to the root symmetry z <-> 1/(lambda z).
    Since lambda is an integer here, we can clear denominators and test exact equality.
    """
    r = len(coeffs) - 1
    if r <= 0:
        return {"ok": False, "reason": "degree<=0", "degree": r}

    # Delta(1/(lambda z)) = sum_k c_k (lambda z)^(-k) = sum_k c_k lambda^{-k} z^{-k}
    # z^r * Delta(1/(lambda z)) = sum_k c_k lambda^{-k} z^{r-k}.
    # Multiply by lambda^r to clear denominators:
    # lambda^r z^r Delta(1/(lambda z)) = sum_k c_k lambda^{r-k} z^{r-k}.
    lhs = [Fraction(0) for _ in range(r + 1)]
    lam = Fraction(lambda_pf, 1)
    for k, ck in enumerate(coeffs):
        lhs[r - k] = Fraction(ck, 1) * (lam ** (r - k))

    rhs = [Fraction(ck, 1) for ck in coeffs]

    # Find C by matching the highest-degree coefficient (z^r): lhs[r] = C * rhs[r]
    if rhs[r] == 0:
        return {"ok": False, "reason": "leading coefficient is zero", "degree": r}
    C = lhs[r] / rhs[r]

    diffs = []
    ok = True
    for k in range(r + 1):
        d = lhs[k] - C * rhs[k]
        if d != 0:
            ok = False
            diffs.append({"k": k, "lhs": str(lhs[k]), "rhsC": str(C * rhs[k]), "diff": str(d)})

    return {
        "ok": ok,
        "degree": r,
        "lambda_pf": int(lambda_pf),
        "C": str(C),
        "C_float": float(C),
        "num_mismatched_coeffs": len(diffs),
        "mismatches_head": diffs[:10],
    }


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Check reciprocal-spectrum closure and functional equation criterion")
    # For integer matrices with many exact zero eigenvalues, numerical eigensolvers may return small ~1e-6 noise.
    parser.add_argument("--zero-tol", type=float, default=1e-5, help="Threshold to treat eigenvalues as zero")
    parser.add_argument("--abs-tol", type=float, default=1e-7, help="Absolute tolerance for mu <-> lambda/mu pairing")
    parser.add_argument("--rel-tol", type=float, default=1e-7, help="Relative tolerance for mu <-> lambda/mu pairing")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output")
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/reciprocal_spectrum_functional_equation_check.json)",
    )
    args = parser.parse_args()

    prog = Progress(label="reciprocal-spectrum-check", every_seconds=20.0)
    print("[reciprocal-spectrum-check] start", flush=True)

    # --- 10-state kernel (B) ---
    from exp_sync_kernel_primitive_spectrum import B_MATRIX, det_poly_coeffs

    B = np.array(B_MATRIX, dtype=float)
    eigB = np.linalg.eigvals(B)
    lamB = perron_root_from_eigs(eigB)
    stats_B = reciprocal_pairing_check(
        eigB,
        lamB,
        zero_tol=args.zero_tol,
        abs_tol=args.abs_tol,
        rel_tol=args.rel_tol,
        prog=prog,
    )
    eigs_B_nonzero = filtered_nonzero_eigs(eigB, zero_tol=args.zero_tol)

    # Exact coefficient-level reciprocity test for 10-state (lambda is expected to be 3).
    # We compute Delta_B(z)=det(I - zB) coefficients exactly (integer).
    coeffs_B = det_poly_coeffs(B_MATRIX, prog)
    # Perron root for B is exactly 3 in the accompanying experiment.
    recip_poly_B = poly_lambda_reciprocity_check_integer_coeffs(coeffs_B, lambda_pf=3)

    # --- 40-state real-input kernel (M) at theta=(0,0,0) ---
    from exp_sync_kernel_real_input_40 import (
        build_kernel_edges,
        build_kernel_map,
        build_real_input_matrix_int,
        build_real_input_states,
    )

    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()
    M_int = build_real_input_matrix_int(states, kernel_map)
    M = np.array(M_int, dtype=float)
    eigM = np.linalg.eigvals(M)
    lamM = perron_root_from_eigs(eigM)
    stats_M = reciprocal_pairing_check(
        eigM,
        lamM,
        zero_tol=args.zero_tol,
        abs_tol=args.abs_tol,
        rel_tol=args.rel_tol,
        prog=prog,
    )
    eigs_M_nonzero = filtered_nonzero_eigs(eigM, zero_tol=args.zero_tol)

    payload: Dict[str, object] = {
        "params": {"zero_tol": args.zero_tol, "abs_tol": args.abs_tol, "rel_tol": args.rel_tol},
        "kernel_10_state_B": {
            "lambda_pf_numeric": float(lamB),
            "eigs_nonzero_sorted": [_as_json_complex(z) for z in eigs_B_nonzero],
            "pairing": stats_B.__dict__,
            "det_I_minus_zB_coeffs": coeffs_B,
            "det_reciprocity_coeff_check_lambda_eq_3": recip_poly_B,
        },
        "kernel_40_state_real_input": {
            "lambda_pf_numeric": float(lamM),
            "eigs_nonzero_sorted": [_as_json_complex(z) for z in eigs_M_nonzero],
            "pairing": stats_M.__dict__,
        },
    }

    if not args.no_output:
        out_path = Path(args.output) if args.output else export_dir() / "reciprocal_spectrum_functional_equation_check.json"
        write_json(out_path, payload)
        print(f"[reciprocal-spectrum-check] wrote {out_path}", flush=True)

    print(
        f"[reciprocal-spectrum-check] B: lambda~{lamB:.12g}, nonzero={stats_B.nonzero_count}, matched={stats_B.matched_count}, "
        f"unmatched={len(stats_B.unmatched)}",
        flush=True,
    )
    print(
        f"[reciprocal-spectrum-check] M40: lambda~{lamM:.12g}, nonzero={stats_M.nonzero_count}, matched={stats_M.matched_count}, "
        f"unmatched={len(stats_M.unmatched)}",
        flush=True,
    )
    print("[reciprocal-spectrum-check] done", flush=True)


if __name__ == "__main__":
    main()

