#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Chebyshev–Dwork congruence chain in the invariant coordinate t=u+u^{-1}.

We work with the weighted sync-kernel trace polynomials:
  a_n(u) = Tr(B(u)^n) in Z[u],
which satisfy the palindromic relation a_n(u)=u^n a_n(1/u).

For even n, define the invariant polynomial A_n(t) in Z[t] by:
  a_n(u) = u^{n/2} A_n(u+u^{-1}).

For p=2 and k>=2, the Dwork congruence implies the closed recursion in Z[t]:
  A_{2^k}(t) ≡ A_{2^{k-1}}(t^2-2) (mod 2^k).

This script computes A_{2^k}(t) for small k and verifies the congruence
coefficientwise, producing an auditable table.

Outputs:
  - artifacts/export/sync_kernel_weighted_chebyshev_dwork_chain.json
  - sections/generated/tab_sync_kernel_weighted_chebyshev_dwork_chain.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress
from exp_sync_kernel_weighted_pressure import STATES, build_edges


Poly = List[int]  # coefficients low->high
MatPoly = List[List[Poly]]


def _poly_trim(a: Poly) -> Poly:
    i = len(a) - 1
    while i > 0 and a[i] == 0:
        i -= 1
    return a[: i + 1]


def _poly_add_inplace(out: Poly, a: Poly) -> None:
    if len(a) > len(out):
        out.extend([0] * (len(a) - len(out)))
    for i, ai in enumerate(a):
        out[i] += ai


def _poly_add_scaled_inplace(out: Poly, a: Poly, s: int) -> None:
    if s == 0:
        return
    if len(a) > len(out):
        out.extend([0] * (len(a) - len(out)))
    for i, ai in enumerate(a):
        out[i] += s * ai


def _poly_mul(a: Poly, b: Poly) -> Poly:
    if len(a) == 1 and a[0] == 0:
        return [0]
    if len(b) == 1 and b[0] == 0:
        return [0]
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if bj == 0:
                continue
            out[i + j] += ai * bj
    return _poly_trim(out)


def _poly_mul_add_inplace(out: Poly, a: Poly, b: Poly) -> None:
    if len(a) == 1 and a[0] == 0:
        return
    if len(b) == 1 and b[0] == 0:
        return
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if bj == 0:
                continue
            out[i + j] += ai * bj


def _poly_compose(f: Poly, g: Poly) -> Poly:
    """Return f(g(t)) with coefficients in Z."""
    out: Poly = [0]
    for a in reversed(f):
        out = _poly_mul(out, g)
        out[0] += a
    return _poly_trim(out)


def _matpoly_build_B_u() -> MatPoly:
    idx = {s: i for i, s in enumerate(STATES)}
    n = len(STATES)
    # Degree-1 polynomials in u: [c0, c1] = c0 + c1*u
    B: MatPoly = [[[0, 0] for _ in range(n)] for _ in range(n)]
    for e in build_edges():
        i = idx[e.src]
        j = idx[e.dst]
        if e.e == 0:
            B[i][j][0] += 1
        else:
            B[i][j][1] += 1
    # Trim zeros to canonical representation [0].
    for i in range(n):
        for j in range(n):
            B[i][j] = _poly_trim(B[i][j])
    return B


def _matpoly_mul(A: MatPoly, B: MatPoly) -> MatPoly:
    n = len(A)
    degA = max(len(A[i][j]) - 1 for i in range(n) for j in range(n))
    degB = max(len(B[i][j]) - 1 for i in range(n) for j in range(n))
    deg = degA + degB
    C: MatPoly = [[[0] * (deg + 1) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for k in range(n):
            a_ik = A[i][k]
            if len(a_ik) == 1 and a_ik[0] == 0:
                continue
            for j in range(n):
                b_kj = B[k][j]
                if len(b_kj) == 1 and b_kj[0] == 0:
                    continue
                _poly_mul_add_inplace(C[i][j], a_ik, b_kj)
    # Normalize entries by trimming.
    for i in range(n):
        for j in range(n):
            C[i][j] = _poly_trim(C[i][j])
    return C


def _matpoly_trace(A: MatPoly) -> Poly:
    n = len(A)
    out: Poly = [0]
    for i in range(n):
        _poly_add_inplace(out, A[i][i])
    return _poly_trim(out)


def _chebyshev_C_list(k_max: int) -> List[Poly]:
    """Return C_k(t) = u^k + u^{-k} as polynomials in t=u+u^{-1}, for k<=k_max."""
    if k_max < 0:
        raise ValueError("k_max must be >= 0")
    C: List[Poly] = []
    C.append([2])  # C_0(t)=2
    if k_max == 0:
        return C
    C.append([0, 1])  # C_1(t)=t
    for k in range(2, k_max + 1):
        # C_k = t*C_{k-1} - C_{k-2}
        tc1 = [0] + C[k - 1]
        out = tc1[:]  # copy
        c2 = C[k - 2]
        if len(c2) > len(out):
            out.extend([0] * (len(c2) - len(out)))
        for i, ci in enumerate(c2):
            out[i] -= ci
        C.append(_poly_trim(out))
    return C


def _A_from_palindromic_trace_coeffs(a: Poly, n: int, C: List[Poly]) -> Poly:
    """Return A_n(t) from a_n(u)=sum_j a[j] u^j, using palindromicity."""
    if n % 2 != 0:
        raise ValueError("Require even n.")
    if len(a) < n + 1:
        a = a + [0] * (n + 1 - len(a))
    if len(a) != n + 1:
        raise ValueError("a has wrong length")

    # Palindromic check: a_j = a_{n-j}.
    for j in range(n + 1):
        if a[j] != a[n - j]:
            raise ValueError(f"Trace is not palindromic at n={n}: a[{j}]!=a[{n-j}]")

    m = n // 2
    out: Poly = [int(a[m])]  # exponent 0 term of u^{-m} a(u)
    for k in range(1, m + 1):
        out = out + [0] * (k + 1 - len(out))
        _poly_add_scaled_inplace(out, C[k], int(a[m + k]))
    return _poly_trim(out)


@dataclass(frozen=True)
class Row:
    k: int
    n: int
    deg_A: int
    congruence_mod_2_pow_k_holds: bool


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify Chebyshev–Dwork congruence chain for the weighted sync-kernel.")
    parser.add_argument("--k-max", type=int, default=6, help="Compute n=2^k up to k-max (k>=2 checked).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_weighted_chebyshev_dwork_chain.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_weighted_chebyshev_dwork_chain.tex"),
    )
    args = parser.parse_args()

    k_max = int(args.k_max)
    if k_max < 2:
        raise SystemExit("Require --k-max >= 2.")

    prog = Progress("sync-kernel-chebyshev-dwork", every_seconds=20.0)
    Bu = _matpoly_build_B_u()
    C = _chebyshev_C_list(2 ** (k_max - 1))

    # Compute B(u)^(2^k) iteratively by squaring, storing trace polynomials.
    M = Bu
    a_pow: Dict[int, Poly] = {}
    for k in range(1, k_max + 1):
        M = _matpoly_mul(M, M)
        n = 2**k
        a_pow[n] = _matpoly_trace(M)
        prog.tick(f"trace n=2^{k}={n}")

    # Build A_{2^k}(t) for k>=1 (n even) as integer coefficient lists.
    A: Dict[int, Poly] = {}
    for k in range(1, k_max + 1):
        n = 2**k
        A[n] = _A_from_palindromic_trace_coeffs(a_pow[n], n=n, C=C)
        prog.tick(f"A_n n={n}")

    # Verify the congruence chain for k>=2.
    rows: List[Row] = []
    for k in range(2, k_max + 1):
        n = 2**k
        n_prev = 2 ** (k - 1)
        lhs = A[n]
        rhs = _poly_compose(A[n_prev], [-2, 0, 1])  # t^2-2
        deg_A = len(_poly_trim(lhs)) - 1
        # Check coefficientwise divisibility by 2^k.
        mod = 2**k
        d = max(len(lhs), len(rhs))
        ok = True
        for i in range(d):
            a = lhs[i] if i < len(lhs) else 0
            b = rhs[i] if i < len(rhs) else 0
            if (a - b) % mod != 0:
                ok = False
                break
        rows.append(Row(k=k, n=n, deg_A=int(deg_A), congruence_mod_2_pow_k_holds=bool(ok)))
        prog.tick(f"check k={k} mod=2^{k}")

    payload = {
        "k_max": k_max,
        "rows": [asdict(r) for r in rows],
        "note": "Check is coefficientwise in Z[t].",
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[chebyshev-dwork] wrote {jout}", flush=True)

    # TeX table.
    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Chebyshev--Dwork congruence chain audit in $\\mathbb{Z}[t]$ for the weighted sync-kernel. "
        "We compute $A_{2^k}(t)$ from $a_{2^k}(u)=\\mathrm{Tr}(B(u)^{2^k})$ via "
        "$a_{2^k}(u)=u^{2^{k-1}}A_{2^k}(u+u^{-1})$, and verify "
        "$A_{2^k}(t)\\equiv A_{2^{k-1}}(t^2-2)\\ (\\mathrm{mod}\\ 2^k)$ coefficientwise.}"
    )
    lines.append("\\label{tab:sync_kernel_weighted_chebyshev_dwork_chain}")
    lines.append("\\begin{tabular}{r r r l}")
    lines.append("\\toprule")
    lines.append("$k$ & $2^k$ & $\\deg A_{2^k}$ & check in $\\mathbb{Z}[t]$\\\\")
    lines.append("\\midrule")
    for r in rows:
        verdict = "PASS" if r.congruence_mod_2_pow_k_holds else "FAIL"
        lines.append(f"{r.k} & {r.n} & {r.deg_A} & {verdict}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[chebyshev-dwork] wrote {tout}", flush=True)
    print("[chebyshev-dwork] done", flush=True)


if __name__ == "__main__":
    main()

