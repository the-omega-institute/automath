#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
p-adic unit-root experiment for the weighted sync-kernel traces a_n(u)=Tr(B(u)^n).

We work modulo p^N with integer representatives for u in Z/p^N Z.
For odd p and u=-1, we have u^p=u exactly in Z, hence also mod p^N.
More generally, for a in F_p^× one can approximate its Teichmüller lift by repeated p-powering.

We verify the Dwork-type congruence on evaluations:
  a_{p^k}(u) ≡ a_{p^{k-1}}(u^p) (mod p^k),
and in the fixed-point case u^p=u we get the Cauchy property:
  a_{p^k}(u) ≡ a_{p^{k-1}}(u) (mod p^k).

Outputs:
  - artifacts/export/sync_kernel_weighted_padic_unit_root.json
  - sections/generated/tab_sync_kernel_weighted_padic_unit_root.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress

from exp_sync_kernel_weighted_pressure import STATES, build_edges


def _matmul_mod(A: List[List[int]], B: List[List[int]], mod: int) -> List[List[int]]:
    n = len(A)
    m = len(B[0])
    k = len(B)
    out = [[0] * m for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        for t in range(k):
            a = Ai[t]
            if a == 0:
                continue
            Bt = B[t]
            for j in range(m):
                out[i][j] = (out[i][j] + a * Bt[j]) % mod
    return out


def _matpow_trace_mod(M: List[List[int]], n: int, mod: int) -> int:
    """Return Tr(M^n) mod mod using fast exponentiation."""
    if n < 0:
        raise ValueError("n must be >= 0")
    size = len(M)
    # identity
    R = [[0] * size for _ in range(size)]
    for i in range(size):
        R[i][i] = 1
    A = M
    e = n
    while e > 0:
        if e & 1:
            R = _matmul_mod(R, A, mod)
        e >>= 1
        if e:
            A = _matmul_mod(A, A, mod)
    tr = 0
    for i in range(size):
        tr = (tr + R[i][i]) % mod
    return tr


def _build_B_mod(u: int, mod: int) -> List[List[int]]:
    edges = build_edges()
    idx = {s: i for i, s in enumerate(STATES)}
    n = len(STATES)
    B = [[0] * n for _ in range(n)]
    u_mod = u % mod
    for e in edges:
        i = idx[e.src]
        j = idx[e.dst]
        w = 1 if e.e == 0 else u_mod
        B[i][j] = (B[i][j] + w) % mod
    return B


def _teichmueller_lift_mod(a: int, p: int, N: int) -> int:
    """Return a Teichmüller lift approximation mod p^N via repeated p-powering."""
    if p <= 2:
        raise ValueError("p must be odd")
    if not (1 <= a <= p - 1):
        raise ValueError("a must be in 1..p-1")
    mod = p**N
    x = a % mod
    # Repeated p-powering converges to ω(a) in Z_p.
    for _ in range(N + 2):
        x = pow(x, p, mod)
    return x


@dataclass(frozen=True)
class Row:
    k: int
    n: int
    a_mod: int
    diff_to_prev_mod_p_pow_k: int
    dwork_defect_mod_p_pow_k: int


def main() -> None:
    parser = argparse.ArgumentParser(description="p-adic unit-root experiment for weighted sync-kernel.")
    parser.add_argument("--p", type=int, default=5, help="Odd prime.")
    parser.add_argument("--N", type=int, default=12, help="Work modulo p^N.")
    parser.add_argument("--k-max", type=int, default=6, help="Compute n=p^k up to k-max.")
    parser.add_argument(
        "--u",
        type=str,
        default="minus1",
        help="Choose u: 'minus1', 'one', or 'teich:a' (a in 1..p-1).",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_weighted_padic_unit_root.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_weighted_padic_unit_root.tex"),
    )
    args = parser.parse_args()

    p = int(args.p)
    if p <= 2 or any(p % q == 0 for q in range(3, int(p**0.5) + 1, 2)):
        raise SystemExit("Require an odd prime p.")
    N = int(args.N)
    if N < 1:
        raise SystemExit("Require N>=1.")
    k_max = int(args.k_max)
    if k_max < 1:
        raise SystemExit("Require k-max>=1.")

    mod = p**N
    u_spec = str(args.u).strip()
    if u_spec == "minus1":
        u = -1
        u_label = "u=-1"
    elif u_spec == "one":
        u = 1
        u_label = "u=1"
    elif u_spec.startswith("teich:"):
        a = int(u_spec.split(":", 1)[1])
        u = _teichmueller_lift_mod(a=a, p=p, N=N)
        u_label = f"u=teich({a})"
    else:
        raise SystemExit("Invalid --u. Use minus1, one, or teich:a")

    prog = Progress("sync-kernel-weighted-padic-unit-root", every_seconds=20.0)

    u_mod = int(u % mod)
    u_p_mod = pow(u_mod, p, mod)
    B = _build_B_mod(u=u_mod, mod=mod)
    B_up = _build_B_mod(u=u_p_mod, mod=mod)
    rows: List[Row] = []
    prev = None
    for k in range(0, k_max + 1):
        n = p**k
        a_mod = _matpow_trace_mod(B, n=n, mod=mod)
        if prev is None:
            diff = 0
        else:
            diff = (a_mod - prev) % (p**k if k >= 1 else 1)
        if k == 0:
            defect = 0
        else:
            a_prev_up_mod = _matpow_trace_mod(B_up, n=p ** (k - 1), mod=mod)
            defect = (a_mod - a_prev_up_mod) % (p**k)
        rows.append(
            Row(
                k=k,
                n=n,
                a_mod=a_mod,
                diff_to_prev_mod_p_pow_k=diff,
                dwork_defect_mod_p_pow_k=defect,
            )
        )
        prev = a_mod
        prog.tick(f"k={k}/{k_max} n={n}")

    # Write JSON.
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "p": p,
        "N": N,
        "mod": mod,
        "u_label": u_label,
        "u_mod": u_mod,
        "u_p_mod": u_p_mod,
        "rows": [asdict(r) for r in rows],
        "note": (
            "dwork_defect_mod_p_pow_k should be 0 when the Dwork congruence "
            "a_{p^k}(u) ≡ a_{p^{k-1}}(u^p) (mod p^k) holds on evaluations. "
            "diff_to_prev_mod_p_pow_k is the fixed-point Cauchy check when u^p=u."
        ),
    }
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[padic-unit-root] wrote {jout}", flush=True)

    # Write LaTeX table.
    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{p-adic unit-root experiment for the weighted sync-kernel. "
        "We compute $a_{p^k}(u)=\\mathrm{Tr}(B(u)^{p^k})$ modulo $p^N$ and report the "
        "Dwork-type defect $a_{p^k}(u)-a_{p^{k-1}}(u^p)$ modulo $p^k$. "
        "In the fixed-point case $u^p=u$, we also report the Cauchy check "
        "$a_{p^k}(u)-a_{p^{k-1}}(u)$ modulo $p^k$.}"
    )
    lines.append("\\label{tab:sync_kernel_weighted_padic_unit_root}")
    lines.append("\\begin{tabular}{r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$k$ & $p^k$ & $a_{p^k}(u)\\bmod p^N$ & "
        "$a_{p^k}(u)-a_{p^{k-1}}(u)\\bmod p^k$ & "
        "$a_{p^k}(u)-a_{p^{k-1}}(u^p)\\bmod p^k$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.k} & {r.n} & {r.a_mod} & {r.diff_to_prev_mod_p_pow_k} & {r.dwork_defect_mod_p_pow_k}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[padic-unit-root] wrote {tout}", flush=True)
    print("[padic-unit-root] done", flush=True)


if __name__ == "__main__":
    main()

