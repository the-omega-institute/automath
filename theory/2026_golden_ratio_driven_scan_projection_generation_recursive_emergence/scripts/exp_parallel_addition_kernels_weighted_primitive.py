#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Compute weighted primitive-orbit fingerprints B_{K,n}(u) for 9/13/21-local kernels.

Key idea (single-flow, exact):
We work directly on the finite single-flow state graph Gamma_K compiled by BFS.
Each labeled transition contributes a monomial weight u^{kappa(e)}. This yields a
weighted adjacency matrix M(u) with entries in Z[u].

We compute the trace polynomials
  a_n(u) := Tr(M(u)^n) in Z[u]
exactly by sparse polynomial matrix powering (no enumeration over |B|^n input words).

Finally, we apply Witt/Möbius inversion:
  B_n(u) = (1/n) * sum_{d|n} mu(d) * a_{n/d}(u^d).

Outputs:
- artifacts/export/parallel_addition_kernels_weighted_primitive.json
- sections/generated/tab_parallel_addition_kernels_weighted_primitive.tex
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

from common_paths import export_dir, generated_dir

import exp_parallel_addition_kernels_bfs as bfs


def _write_text(p: Path, s: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(s, encoding="utf-8")


def _mobius(n: int) -> int:
    if n == 1:
        return 1
    x = n
    mu = 1
    p = 2
    while p * p <= x:
        if x % p == 0:
            x //= p
            mu = -mu
            if x % p == 0:
                return 0
            while x % p == 0:
                x //= p
        p += 1 if p == 2 else 2
    if x > 1:
        mu = -mu
    return mu


def _divisors(n: int) -> List[int]:
    ds: List[int] = []
    d = 1
    while d * d <= n:
        if n % d == 0:
            ds.append(d)
            if d * d != n:
                ds.append(n // d)
        d += 1
    return sorted(ds)


def _poly_trim(p: List[int]) -> List[int]:
    i = len(p) - 1
    while i > 0 and p[i] == 0:
        i -= 1
    return p[: i + 1]


def _poly_mul(a: List[int], b: List[int]) -> List[int]:
    if a == [0] or b == [0]:
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


def _poly_pow(p: List[int], n: int) -> List[int]:
    if n < 0:
        raise ValueError("n must be >= 0")
    if n == 0:
        return [1]
    if n == 1:
        return p[:]
    out = [1]
    base = p[:]
    e = n
    while e:
        if e & 1:
            out = _poly_mul(out, base)
        e >>= 1
        if e:
            base = _poly_mul(base, base)
    return _poly_trim(out)


def _trace_polys_closed_form_k9(n_max: int) -> Dict[int, List[int]]:
    """
    For the 9-local (strong) single-flow compiled machine, kappa(e)∈{0,1} and
    each step has exactly 7 symbols with kappa=0 and 14 symbols with kappa=1.
    Therefore:
      a_n(u) = Tr(M(u)^n) = (7 + 14u)^n.
    """
    a1 = [7, 14]
    return {n: _poly_pow(a1, n) for n in range(1, n_max + 1)}


def _poly_sub_u_pow(p: List[int], d: int) -> List[int]:
    # p(u^d): coeff[k] goes to degree k*d.
    if d == 1:
        return p[:]
    out = [0] * ((len(p) - 1) * d + 1)
    for k, c in enumerate(p):
        if c:
            out[k * d] += c
    return _poly_trim(out)


def _poly_add_scaled(dst: List[int], src: List[int], scale: int) -> List[int]:
    if scale == 0:
        return dst
    if len(dst) < len(src):
        dst.extend([0] * (len(src) - len(dst)))
    for i, c in enumerate(src):
        if c:
            dst[i] += scale * c
    return _poly_trim(dst)


def _poly_eval(p: List[int], u: float) -> float:
    acc = 0.0
    up = 1.0
    for c in p:
        acc += float(c) * up
        up *= u
    return acc


def _poly_to_latex(p: List[int], var: str = "u") -> str:
    terms: List[str] = []
    for k, c in enumerate(p):
        if c == 0:
            continue
        if k == 0:
            terms.append(str(c))
            continue
        if c == 1:
            coef = ""
        else:
            coef = str(c)
        if k == 1:
            mon = var
        else:
            mon = f"{var}^{{{k}}}"
        terms.append(f"{coef}{mon}" if coef else mon)
    if not terms:
        return "0"
    return "+".join(terms)


# -----------------------------
# Exact trace polynomials from BFS-compiled graph
# -----------------------------


SparseMat = List[Dict[int, int]]  # row -> {col: count} with integer counts


def _mat_zero(n: int) -> SparseMat:
    return [dict() for _ in range(n)]


def _mat_add_inplace(dst: SparseMat, src: SparseMat) -> None:
    for i in range(len(dst)):
        if not src[i]:
            continue
        di = dst[i]
        for j, v in src[i].items():
            di[j] = di.get(j, 0) + v


def _mat_mul(A: SparseMat, B: SparseMat) -> SparseMat:
    n = len(A)
    out: SparseMat = _mat_zero(n)
    for i in range(n):
        if not A[i]:
            continue
        oi = out[i]
        for j, aij in A[i].items():
            Bj = B[j]
            if not Bj:
                continue
            for k, bjk in Bj.items():
                oi[k] = oi.get(k, 0) + aij * bjk
    return out


def _trace_from_sparse(M: SparseMat) -> int:
    s = 0
    for i, row in enumerate(M):
        if row:
            s += row.get(i, 0)
    return s


def _build_base_mats(spec: bfs.KernelSpec, *, prog: bfs.Progress) -> Tuple[List[SparseMat], int, int]:
    idx, edges = bfs._bfs_states(spec, prog)
    n_states = len(idx)
    b = len(spec.alphabet)
    kmax = 0
    # First pass: kappa range
    for _i, _j, _a, kA, kB in edges:
        k = int(kA) + int(kB)
        if k > kmax:
            kmax = k
    mats: List[SparseMat] = [_mat_zero(n_states) for _ in range(kmax + 1)]
    for i, j, _a, kA, kB in edges:
        k = int(kA) + int(kB)
        mats[k][i][j] = mats[k][i].get(j, 0) + 1
    return mats, n_states, b


def _trace_polys_from_graph(
    spec: bfs.KernelSpec,
    n_max: int,
    *,
    prog: bfs.Progress,
    label: str,
) -> Dict[int, List[int]]:
    base_mats, n_states, b = _build_base_mats(spec, prog=prog)
    kmax = len(base_mats) - 1

    # power_mats[d] is the coefficient matrix of u^d in M(u)^n.
    power_mats: List[SparseMat] = [m for m in base_mats]
    out: Dict[int, List[int]] = {}

    for n in range(1, n_max + 1):
        deg_max = n * kmax
        coeffs = [0] * (deg_max + 1)
        for d, Md in enumerate(power_mats):
            coeffs[d] = _trace_from_sparse(Md)
        coeffs = _poly_trim(coeffs)
        out[n] = coeffs

        # Sanity: at u=1, trace should be |B|^n for these compiled machines.
        if int(round(_poly_eval(coeffs, 1.0))) != b**n:
            raise RuntimeError(f"trace sanity failed for {label} n={n}: a_n(1) != |B|^n")

        prog.tick(f"{label} traces done n={n} deg={len(coeffs)-1} states={n_states}")

        if n == n_max:
            break

        # Multiply by base: M(u)^{n+1} = M(u)^n * M(u)
        new_mats: List[SparseMat] = [_mat_zero(n_states) for _ in range((n + 1) * kmax + 1)]
        for d, Pd in enumerate(power_mats):
            if not any(Pd):
                continue
            for k, Bk in enumerate(base_mats):
                if not any(Bk):
                    continue
                prod = _mat_mul(Pd, Bk)
                _mat_add_inplace(new_mats[d + k], prod)
                # Ensure long runs remain auditable (at least one line / 20s).
                prog.tick(f"{label} mul n={n}->{n+1} deg={d}+{k}")
        power_mats = new_mats

    return out


def _decode_word(code: int, base: int, n: int, alphabet: Sequence[int]) -> List[int]:
    w = [alphabet[0]] * n
    x = code
    for i in range(n - 1, -1, -1):
        x, r = divmod(x, base)
        w[i] = alphabet[r]
    return w


def _apply_word(spec: bfs.KernelSpec, s: bfs.State, word: Sequence[int]) -> Tuple[bfs.State, int]:
    ksum = 0
    st = s
    for a in word:
        st, k = spec.step(st, int(a))
        ksum += int(k)
    return st, ksum


def _find_fixed_point(
    spec: bfs.KernelSpec,
    word: Sequence[int],
    seed_a: bfs.State,
    seed_b: bfs.State,
    *,
    max_iters: int,
) -> bfs.State:
    def f(st: bfs.State) -> bfs.State:
        return _apply_word(spec, st, word)[0]

    sa = seed_a
    sb = seed_b
    for _ in range(max_iters):
        sa1 = f(sa)
        sb1 = f(sb)
        if sa1 == sa and sb1 == sb:
            if sa != sb:
                raise RuntimeError("word-map has at least two fixed points (seeds converge to different fixed points)")
            return sa
        sa, sb = sa1, sb1
    raise RuntimeError("failed to converge to fixed point within max_iters")


def _trace_polys_by_word_enumeration(
    spec: bfs.KernelSpec,
    n_max: int,
    *,
    max_iters: int,
    prog: bfs.Progress,
    label: str,
) -> Dict[int, List[int]]:
    # This path is only used for K13 by default: its single-flow graph is large,
    # while word enumeration up to n<=4 is still affordable.
    idx, _edges = bfs._bfs_states(spec, prog)
    states = list(idx.keys())
    seed_a = spec.init_state
    seed_b = states[-1] if states else spec.init_state

    b = len(spec.alphabet)
    alphabet = list(spec.alphabet)
    out: Dict[int, List[int]] = {}

    for n in range(1, n_max + 1):
        deg_max = n * 3  # safe upper bound; will trim
        poly = [0] * (deg_max + 1)
        total = b**n
        t0 = time.time()
        for code in range(total):
            if code % max(1, total // 50) == 0 and (time.time() - t0) > 20:
                prog.tick(f"{label} enumerate n={n} {code}/{total}")
                t0 = time.time()
            word = _decode_word(code, b, n, alphabet)
            fp = _find_fixed_point(spec, word, seed_a, seed_b, max_iters=max_iters)
            fp2, ksum = _apply_word(spec, fp, word)
            if fp2 != fp:
                raise RuntimeError("computed fixed point is not fixed under one word application")
            if ksum > deg_max:
                poly.extend([0] * (ksum - deg_max))
                deg_max = ksum
            poly[ksum] += 1
        out[n] = _poly_trim(poly)
        if int(round(_poly_eval(out[n], 1.0))) != total:
            raise RuntimeError(f"trace sanity failed for {label} n={n}: a_n(1) != |B|^n")
        prog.tick(f"{label} traces (enum) done n={n} deg={len(out[n])-1}")
    return out


def _primitive_from_traces_polys(a: Dict[int, List[int]], n_max: int) -> Dict[int, List[int]]:
    B: Dict[int, List[int]] = {}
    for n in range(1, n_max + 1):
        acc: List[int] = [0]
        for d in _divisors(n):
            mu = _mobius(d)
            if mu == 0:
                continue
            m = n // d
            poly_sub = _poly_sub_u_pow(a[m], d)
            acc = _poly_add_scaled(acc, poly_sub, mu)
        # divide by n
        if any(c % n != 0 for c in acc):
            raise RuntimeError(f"non-integer coefficients in primitive inversion at n={n}")
        B[n] = _poly_trim([c // n for c in acc])
    return B


def _make_table(rows: List[Dict[str, str]]) -> str:
    lines: List[str] = []
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\scriptsize")
    lines.append(r"\setlength{\tabcolsep}{6pt}")
    lines.append(r"\renewcommand{\arraystretch}{1.15}")
    lines.append(
        r"\caption{两变量 $\zeta_K(z,u)$ 的 primitive 分层谱指纹：单流同步图上 $B_{K,n}(u)$ 的显式多项式（由脚本 \texttt{scripts/exp\_parallel\_addition\_kernels\_weighted\_primitive.py} 生成）。}"
    )
    lines.append(r"\label{tab:parallel-addition-kernels-weighted-primitive}")
    lines.append(r"\begin{tabular}{@{}lccp{0.62\textwidth}cc@{}}")
    lines.append(r"\toprule")
    lines.append(r"核 & $n$ & $\deg_u$ & $B_{K,n}(u)$ & $B_{K,n}(0)$ & $B_{K,n}(1)$ \\")
    lines.append(r"\midrule")
    for r in rows:
        lines.append(
            " & ".join([r["kernel"], r["n"], r["deg"], r["poly"], r["b0"], r["b1"]]) + r" \\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute weighted primitive polynomials B_{K,n}(u) for 9/13/21-local kernels")
    parser.add_argument("--nmax-9", type=int, default=6)
    parser.add_argument("--nmax-13", type=int, default=4)
    parser.add_argument("--nmax-21", type=int, default=6)
    parser.add_argument("--max-iters", type=int, default=60, help="Max iterations to converge to word fixed point (K13)")
    parser.add_argument(
        "--method-21",
        type=str,
        default="enum",
        choices=["enum", "graph"],
        help="How to compute traces for K21 (enum is exact but grows as 5^n; graph is exact but can be heavy for large n)",
    )
    parser.add_argument("--no-output", action="store_true")
    args = parser.parse_args()

    prog = bfs.Progress(label="par-add-weighted-primitive", every_seconds=20.0)
    print("[par-add-weighted-primitive] start", flush=True)

    specs = bfs._make_specs(max(args.nmax_9, args.nmax_13, args.nmax_21))
    plan = []
    for sp in specs:
        if "9-local" in sp.name:
            plan.append((sp, args.nmax_9))
        elif "13-local" in sp.name:
            plan.append((sp, args.nmax_13))
        else:
            plan.append((sp, args.nmax_21))

    payload: Dict[str, object] = {"kernels": []}
    table_rows: List[Dict[str, str]] = []

    for sp, nmax in plan:
        name_tex = r"$K_{9}$" if "9-local" in sp.name else (r"$K_{13}$" if "13-local" in sp.name else r"$K_{21}$")
        prog.tick(f"{sp.name} begin")
        if "9-local" in sp.name:
            a_polys = _trace_polys_closed_form_k9(nmax)
            prog.tick(f"{sp.name} traces (closed form) done nmax={nmax}")
        elif "13-local" in sp.name:
            a_polys = _trace_polys_by_word_enumeration(
                sp, nmax, max_iters=args.max_iters, prog=prog, label=sp.name
            )
        else:
            if args.method_21 == "graph":
                a_polys = _trace_polys_from_graph(sp, nmax, prog=prog, label=sp.name)
            else:
                a_polys = _trace_polys_by_word_enumeration(
                    sp, nmax, max_iters=args.max_iters, prog=prog, label=sp.name
                )
        B_polys = _primitive_from_traces_polys(a_polys, nmax)

        payload["kernels"].append(
            {
                "name": sp.name,
                "alphabet_B": sp.alphabet,
                "n_max": nmax,
                "a_n_u_poly": {str(n): a_polys[n] for n in sorted(a_polys.keys())},
                "B_n_u_poly": {str(n): B_polys[n] for n in sorted(B_polys.keys())},
            }
        )

        for n in range(1, nmax + 1):
            poly = B_polys[n]
            table_rows.append(
                {
                    "kernel": name_tex,
                    "n": str(n),
                    "poly": f"${_poly_to_latex(poly)}$",
                    "b0": str(int(round(_poly_eval(poly, 0.0)))),
                    "b1": str(int(round(_poly_eval(poly, 1.0)))),
                    "deg": str(len(poly) - 1),
                }
            )

        prog.tick(f"{sp.name} done")

    if not args.no_output:
        out_json = export_dir() / "parallel_addition_kernels_weighted_primitive.json"
        _write_text(out_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"[par-add-weighted-primitive] wrote {out_json}", flush=True)

        out_tex = generated_dir() / "tab_parallel_addition_kernels_weighted_primitive.tex"
        _write_text(out_tex, _make_table(table_rows))
        print(f"[par-add-weighted-primitive] wrote {out_tex}", flush=True)

    print("[par-add-weighted-primitive] done", flush=True)


if __name__ == "__main__":
    main()

