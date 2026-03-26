#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""BFS-compile 9/13/21-local phi-kernels into online state graphs (single-flow).

This script turns the slide/paper pseudocode for the golden-ratio parallel-addition
kernels (SRZ/WRZ/Algorithm-G) into *deterministic online machines* on a single
congruence-class stream (mod 4 for ±4 stencil, mod 2 for ±2 stencil).

We then:
- BFS all reachable states (finite);
- compute stationary distribution under *uniform IID input symbols*;
- report the per-step activity kappa distribution (# nonzero q events decided now);
- compute carry-free (u=0) skeleton zeta determinants and primitive spectra.

Outputs:
- artifacts/export/parallel_addition_kernels_bfs.json
- sections/generated/tab_parallel_addition_kernels_bfs.tex
"""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Deque, Dict, Iterable, List, Mapping, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


State = Tuple[int, ...]


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _fmt(x: float, digits: int = 12) -> str:
    return f"{x:.{digits}g}"


def _mobius(n: int) -> int:
    if n == 1:
        return 1
    mu = 1
    p = 2
    nn = n
    while p * p <= nn:
        if nn % p == 0:
            nn //= p
            if nn % p == 0:
                return 0
            mu = -mu
        p += 1
    if nn > 1:
        mu = -mu
    return mu


def _divisors(n: int) -> List[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def _primitive_from_traces(traces: List[int]) -> List[int]:
    out: List[int] = []
    for n in range(1, len(traces) + 1):
        s = 0
        for d in _divisors(n):
            s += _mobius(d) * traces[n // d - 1]
        if s % n != 0:
            raise ValueError(f"non-integer primitive at n={n}: {s}/{n}")
        out.append(s // n)
    return out


def _power_iteration(
    n: int,
    mul: Callable[[List[float]], List[float]],
    itmax: int,
    tol: float,
    prog: Progress,
    label: str,
) -> float:
    # Positive start vector, normalized so sum(x)=1.
    x = [1.0 / n] * n
    lam = 0.0
    for it in range(1, itmax + 1):
        y = mul(x)
        # With sum(x)=1 and nonnegative operator, sum(y)=sum(Mx) is a stable scalar
        # that converges to the PF eigenvalue when x approaches the PF eigenvector.
        s = sum(y)
        if s <= 0.0:
            return 0.0
        y = [v / s for v in y]
        lam_new = s
        if it > 50 and abs(lam_new - lam) / max(1.0, abs(lam_new)) < tol:
            prog.tick(f"{label} power it={it} lam~{lam_new:.12g}")
            return lam_new
        lam = lam_new
        x = y
        if it % 200 == 0:
            prog.tick(f"{label} power it={it} lam~{lam_new:.12g}")
    return lam


def _power_iteration_nonneg_inplace(
    n: int,
    mul_inplace,
    *,
    itmax: int,
    tol: float,
    prog: Progress,
    label: str,
) -> float:
    """Power iteration with reusable NumPy buffers (nonnegative operator)."""
    if n <= 0:
        return 0.0
    x = np.full(n, 1.0 / n, dtype=float)
    y = np.empty_like(x)
    lam = 0.0
    for it in range(1, itmax + 1):
        mul_inplace(x, y)
        s = float(np.sum(y))
        if not (s > 0.0):
            return 0.0
        y *= 1.0 / s
        lam_new = s
        if it > 50 and abs(lam_new - lam) / max(1.0, abs(lam_new)) < tol:
            prog.tick(f"{label} power it={it} lam~{lam_new:.12g}")
            return lam_new
        lam = lam_new
        x, y = y, x
        if it % 200 == 0:
            prog.tick(f"{label} power it={it} lam~{lam_new:.12g}")
    return lam


@dataclass(frozen=True)
class KernelSpec:
    name: str
    block_size: int  # digits per block (4 for ±4 stencil, 2 for ±2 stencil)
    alphabet: List[int]
    init_state: State
    step: Callable[[State, int], Tuple[State, int]]  # (next_state, kappa)
    # carry-free skeleton (u=0) on *input symbols*:
    carry_free_symbols: List[int]
    carry_free_det: str
    carry_free_traces: List[int]


def _bfs_states(spec: KernelSpec, prog: Progress) -> Tuple[Dict[State, int], List[Tuple[int, int, int, int, int]]]:
    idx: Dict[State, int] = {spec.init_state: 0}
    q: Deque[State] = deque([spec.init_state])
    # (src_id, dst_id, input_symbol, kappa_A, kappa_B)
    # For K21, kappa_A and kappa_B correspond to the two elimination phases.
    # For other kernels, we set kappa_A=kappa and kappa_B=0.
    edges: List[Tuple[int, int, int, int, int]] = []
    b = len(spec.alphabet)
    steps = 0
    while q:
        s = q.popleft()
        sid = idx[s]
        for a in spec.alphabet:
            ns, kappa = spec.step(s, a)
            if ns not in idx:
                idx[ns] = len(idx)
                q.append(ns)
            if "21-local" in spec.name:
                # In our implementation, kappa = 1_{qA!=0}+1_{qB!=0}.
                # Recover components deterministically by recomputing them here.
                kA, kB = _kappa_split_21_local(s, a)
                edges.append((sid, idx[ns], int(a), int(kA), int(kB)))
            else:
                edges.append((sid, idx[ns], int(a), int(kappa), 0))
            steps += 1
        if steps % (b * 5000) == 0:
            prog.tick(f"{spec.name} bfs states={len(idx)} edges={len(edges)}")
    return idx, edges


def _stationary_uniform_inputs(
    n_states: int,
    edges: List[Tuple[int, int, int, int, int]],
    b: int,
    prog: Progress,
    label: str,
) -> List[float]:
    # Transition matrix is average over input symbols: P_ij = (# of inputs sending i->j)/b.
    out: List[Dict[int, int]] = [dict() for _ in range(n_states)]
    for i, j, _a, _kA, _kB in edges:
        out_i = out[i]
        out_i[j] = out_i.get(j, 0) + 1

    pi = [1.0 / n_states] * n_states
    for it in range(1, 20000 + 1):
        new = [0.0] * n_states
        for i in range(n_states):
            if pi[i] == 0.0:
                continue
            for j, c in out[i].items():
                new[j] += pi[i] * (c / b)
        s = sum(new)
        if s > 0:
            new = [v / s for v in new]
        diff = sum(abs(new[i] - pi[i]) for i in range(n_states))
        pi = new
        if diff < 1e-13 and it > 200:
            prog.tick(f"{label} stationary it={it} diff={diff:.3e}")
            break
        if it % 1000 == 0:
            prog.tick(f"{label} stationary it={it} diff={diff:.3e}")
    return pi


def _stationary_uniform_inputs_from_arrays(
    *,
    n_states: int,
    src: np.ndarray,
    dst: np.ndarray,
    b: int,
    prog: Progress,
    label: str,
) -> np.ndarray:
    """Stationary distribution under uniform IID inputs, using sparse scatter-add."""
    if n_states <= 0:
        return np.zeros(0, dtype=float)
    inv_b = 1.0 / float(b)
    pi = np.full(n_states, inv_b * (float(b) / float(n_states)), dtype=float)
    new = np.empty_like(pi)
    tmp = np.empty(src.shape[0], dtype=float)
    for it in range(1, 20000 + 1):
        # new[dst] += pi[src] / b
        np.take(pi, src, out=tmp)
        new.fill(0.0)
        np.add.at(new, dst, tmp)
        new *= inv_b
        s = float(np.sum(new))
        if s > 0.0:
            new *= 1.0 / s
        diff = float(np.sum(np.abs(new - pi)))
        pi, new = new, pi
        if diff < 1e-13 and it > 200:
            prog.tick(f"{label} stationary it={it} diff={diff:.3e}")
            break
        if it % 1000 == 0:
            prog.tick(f"{label} stationary it={it} diff={diff:.3e}")
    return pi


def _kappa_dist(
    edges: List[Tuple[int, int, int, int, int]],
    pi: List[float],
    b: int,
) -> Dict[int, float]:
    # Under uniform input, from state i each input has prob 1/b.
    d: Dict[int, float] = {}
    for i, _j, _a, kA, kB in edges:
        k = int(kA) + int(kB)
        d[k] = d.get(k, 0.0) + pi[i] / b
    s = sum(d.values())
    if s == 0.0:
        return {k: 0.0 for k in sorted(d.keys())}
    return {k: v / s for k, v in sorted(d.items())}


def _kappa_dist_from_arrays(
    *,
    src: np.ndarray,
    kappa: np.ndarray,
    pi: np.ndarray,
    b: int,
) -> Dict[int, float]:
    inv_b = 1.0 / float(b)
    tmp = np.empty(src.shape[0], dtype=float)
    np.take(pi, src, out=tmp)
    tmp *= inv_b
    k_int = kappa.astype(np.int64, copy=False)
    max_k = int(np.max(k_int)) if k_int.size else 0
    hist = np.bincount(k_int, weights=tmp, minlength=max_k + 1)
    s = float(np.sum(hist))
    if not (s > 0.0):
        return {}
    hist = hist / s
    out: Dict[int, float] = {}
    for k, p in enumerate(hist.tolist()):
        if p:
            out[int(k)] = float(p)
    return out


def _kappa_split_probs(
    edges: List[Tuple[int, int, int, int, int]],
    pi: List[float],
    b: int,
) -> Tuple[float, float]:
    # Return (P(kappa_A>0), P(kappa_B>0)) under stationary pi and uniform inputs.
    pA = 0.0
    pB = 0.0
    for i, _j, _a, kA, kB in edges:
        w = pi[i] / b
        if kA:
            pA += w
        if kB:
            pB += w
    return pA, pB


def _kappa_split_probs_from_arrays(
    *,
    src: np.ndarray,
    kA: np.ndarray,
    kB: np.ndarray,
    pi: np.ndarray,
    b: int,
) -> Tuple[float, float]:
    inv_b = 1.0 / float(b)
    tmp = np.empty(src.shape[0], dtype=float)
    np.take(pi, src, out=tmp)
    tmp *= inv_b
    pA = float(np.sum(tmp[kA != 0]))
    pB = float(np.sum(tmp[kB != 0]))
    return pA, pB


def _lambda_u(
    n_states: int,
    edges: List[Tuple[int, int, int, int, int]],
    u: float,
    prog: Progress,
    label: str,
) -> float:
    # Spectral radius of weighted adjacency M(u), where each labeled edge contributes u^kappa.
    # We do power iteration on the linear operator (sparse).
    out: List[List[Tuple[int, int]]] = [[] for _ in range(n_states)]  # (dst, kappa)
    for i, j, _a, kA, kB in edges:
        out[i].append((j, int(kA) + int(kB)))

    def mul(x: List[float]) -> List[float]:
        y = [0.0] * n_states
        if u == 0.0:
            for i in range(n_states):
                xi = x[i]
                if xi == 0.0:
                    continue
                for j, k in out[i]:
                    if k == 0:
                        y[j] += xi
            return y
        for i in range(n_states):
            xi = x[i]
            if xi == 0.0:
                continue
            for j, k in out[i]:
                y[j] += xi * (u**k)
        return y

    return _power_iteration(n_states, mul, itmax=8000, tol=1e-12, prog=prog, label=f"{label} u={u}")


def _lambda_u_from_arrays(
    *,
    n_states: int,
    src: np.ndarray,
    dst: np.ndarray,
    kappa: np.ndarray,
    u: float,
    prog: Progress,
    label: str,
) -> float:
    """Spectral radius of weighted adjacency M(u), computed by power iteration."""
    if n_states <= 0:
        return 0.0

    k_int = kappa.astype(np.int64, copy=False)
    if u == 0.0:
        mask = k_int == 0
        src0 = src[mask]
        dst0 = dst[mask]

        def mul_inplace(x: np.ndarray, y: np.ndarray) -> None:
            y.fill(0.0)
            np.add.at(y, dst0, x[src0])

        return _power_iteration_nonneg_inplace(
            n_states, mul_inplace, itmax=8000, tol=1e-12, prog=prog, label=f"{label} u={u}"
        )

    # Precompute edge weights w_e = u^{kappa_e}.
    k_max = int(np.max(k_int)) if k_int.size else 0
    pow_u = np.empty(k_max + 1, dtype=float)
    pow_u[0] = 1.0
    for k in range(1, k_max + 1):
        pow_u[k] = pow_u[k - 1] * float(u)
    w_edge = pow_u[k_int]  # shape: (n_edges,)

    tmp = np.empty(src.shape[0], dtype=float)

    def mul_inplace(x: np.ndarray, y: np.ndarray) -> None:
        y.fill(0.0)
        np.take(x, src, out=tmp)
        tmp[:] *= w_edge
        np.add.at(y, dst, tmp)

    return _power_iteration_nonneg_inplace(
        n_states, mul_inplace, itmax=8000, tol=1e-12, prog=prog, label=f"{label} u={u}"
    )


# -----------------------------
# Kernel implementations (single flow)
# -----------------------------


def _q_strong(v: int) -> int:
    # SRZ strong kernel for beta=phi uses B=7, inner alphabet [-3,3].
    # Choose q in {-1,0,1} so that v-7q in [-3,3].
    if v >= 4:
        return 1
    if v <= -4:
        return -1
    return 0


def _step_9_local(state: State, v: int) -> Tuple[State, int]:
    # State: (v_{n-1}, q_{n-2})
    v_prev, q_prev2 = state
    q_prev1 = _q_strong(v_prev)
    q = _q_strong(v)
    # output digit exists but not stored; we count kappa from *newly decided* q.
    # z_{n-1} = v_{n-1} - 7 q_{n-1} + q_{n-2} + q_n
    _ = v_prev - 7 * q_prev1 + q_prev2 + q
    ns = (v, q_prev1)
    kappa = 1 if q != 0 else 0
    return ns, kappa


def _q_weak(z: int) -> int:
    if z >= 2:
        return 1
    if z <= -2:
        return -1
    return 0


def _micro_step(state: State, z: int) -> Tuple[State, int, int]:
    # State: (z_{n-1}, q_{n-2}, q_{n-1})
    z_prev, q_prev2, q_prev1 = state
    q = _q_weak(z)
    out_prev = z_prev - 3 * q_prev1 + q_prev2 + q
    ns = (z, q_prev1, q)
    kappa = 1 if q != 0 else 0
    return ns, out_prev, kappa


def _step_13_local(state: State, v: int) -> Tuple[State, int]:
    # State: 3 micro-stages chained. Each stage state is (z_{n-1}, q_{n-2}, q_{n-1}).
    s1 = (state[0], state[1], state[2])
    s2 = (state[3], state[4], state[5])
    s3 = (state[6], state[7], state[8])

    s1, o1, k1 = _micro_step(s1, v)
    s2, o2, k2 = _micro_step(s2, o1)
    s3, _o3, k3 = _micro_step(s3, o2)

    ns = (
        s1[0],
        s1[1],
        s1[2],
        s2[0],
        s2[1],
        s2[2],
        s3[0],
        s3[1],
        s3[2],
    )
    return ns, (k1 + k2 + k3)


def _qA_algoA(v_prev: int, v: int, v_next: int) -> int:
    # Algorithm A in the 7-page notes uses:
    # q_j = -1 if z_j = -2 OR z_j = -1 OR (z_j=0 and z_{j+2}<0 and z_{j-2}<0), else 0.
    # In flow coordinates (step size 2), neighbors are ±1.
    if v == -2:
        return -1
    if v == -1:
        return -1
    if v == 0 and v_prev < 0 and v_next < 0:
        return -1
    return 0


def _qB_algoB(wm2: int, wm1: int, w0: int, wp1: int, wp2: int) -> int:
    # Algorithm B conditions (flow coordinates: neighbors ±1, ±2).
    if w0 == 2:
        return 1
    if w0 == 1 and (wp1 >= 1 or wm1 >= 1):
        return 1
    if w0 == 0 and wp1 == 2 and wm1 == 2:
        return 1
    if w0 == 0 and wp1 == 1 and wm1 == 1 and wp2 >= 1 and wm2 >= 1:
        return 1
    if w0 == 0 and wp1 == 2 and wm1 == 1 and wm2 >= 1:
        return 1
    if w0 == 0 and wm1 == 2 and wp1 == 1 and wp2 >= 1:
        return 1
    return 0


def _step_21_local(state: State, v_t: int) -> Tuple[State, int]:
    # This is a deterministic online pipeline at single-flow resolution.
    # State layout:
    # (v_{t-2}, v_{t-1},
    #  qA_{t-3}, qA_{t-2},
    #  w_{t-6}, w_{t-5}, w_{t-4}, w_{t-3},
    #  qB_{t-6}, qB_{t-5})
    v_tm2, v_tm1, qA_tm3, qA_tm2, w_tm6, w_tm5, w_tm4, w_tm3, qB_tm6, qB_tm5 = state

    qA_tm1 = _qA_algoA(v_tm2, v_tm1, v_t)
    # w_{t-2} uses qA_{t-1} (new) and qA_{t-2}, qA_{t-3} (stored) and v_{t-2} (stored)
    w_tm2 = v_tm2 - 3 * qA_tm2 + qA_tm3 + qA_tm1

    qB_tm4 = _qB_algoB(w_tm6, w_tm5, w_tm4, w_tm3, w_tm2)

    kappa = (1 if qA_tm1 != 0 else 0) + (1 if qB_tm4 != 0 else 0)

    ns = (
        v_tm1,
        v_t,
        qA_tm2,
        qA_tm1,
        w_tm5,
        w_tm4,
        w_tm3,
        w_tm2,
        qB_tm5,
        qB_tm4,
    )
    return ns, kappa


def _kappa_split_21_local(state: State, v_t: int) -> Tuple[int, int]:
    # Mirror the internal decisions of _step_21_local, but return (kappa_A, kappa_B).
    v_tm2, v_tm1, qA_tm3, qA_tm2, w_tm6, w_tm5, w_tm4, w_tm3, qB_tm6, qB_tm5 = state
    qA_tm1 = _qA_algoA(v_tm2, v_tm1, v_t)
    w_tm2 = v_tm2 - 3 * qA_tm2 + qA_tm3 + qA_tm1
    qB_tm4 = _qB_algoB(w_tm6, w_tm5, w_tm4, w_tm3, w_tm2)
    kA = 1 if qA_tm1 != 0 else 0
    kB = 1 if qB_tm4 != 0 else 0
    return kA, kB


def _carry_free_traces_full_shift(m: int, n_max: int) -> List[int]:
    return [m**n for n in range(1, n_max + 1)]


def _carry_free_traces_golden_mean(n_max: int) -> List[int]:
    # Golden mean adjacency G = [[1,1],[1,0]]
    a, b, c, d = 1, 1, 1, 0
    traces = []
    for n in range(1, n_max + 1):
        traces.append(a + d)
        # multiply by G
        a, b, c, d = a + b, a, c + d, c
    return traces


def _make_specs(n_max_primitive: int) -> List[KernelSpec]:
    # 9-local: input v in [-10,10], carry-free means q=0 <=> v in [-3,3] (7 symbols).
    spec9 = KernelSpec(
        name="9-local (SRZ, A=[-5..5], single-flow)",
        block_size=4,
        alphabet=list(range(-10, 11)),
        init_state=(0, 0),
        step=_step_9_local,
        carry_free_symbols=list(range(-3, 4)),
        carry_free_det="1-7z",
        carry_free_traces=_carry_free_traces_full_shift(7, n_max_primitive),
    )

    # 13-local: input v in [-6,6], carry-free for *all 3 stages* means v in [-1,1] (3 symbols).
    init_micro = (0, 0, 0)
    spec13 = KernelSpec(
        name="13-local (WRZ, A=[-3..3], s=3, single-flow)",
        block_size=2,
        alphabet=list(range(-6, 7)),
        init_state=(
            init_micro[0],
            init_micro[1],
            init_micro[2],
            init_micro[0],
            init_micro[1],
            init_micro[2],
            init_micro[0],
            init_micro[1],
            init_micro[2],
        ),
        step=_step_13_local,
        carry_free_symbols=list(range(-1, 2)),
        carry_free_det="1-3z",
        carry_free_traces=_carry_free_traces_full_shift(3, n_max_primitive),
    )

    # 21-local: input v in [-2,2]. carry-free requires qA=0 and qB=0 at all times.
    # With Algorithm A, qA=0 excludes v=-2,-1 and forbids the (0 with negative neighbors) case.
    # Additionally qB=0 excludes v=2 and forbids adjacent 1s (golden mean) on the remaining {0,1}.
    spec21 = KernelSpec(
        name="21-local (Algorithm G on A={-1,0,1}, single-flow)",
        block_size=2,
        alphabet=list(range(-2, 3)),
        init_state=(0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
        step=_step_21_local,
        carry_free_symbols=[0, 1],  # the carry-free core lives on {0,1} with golden-mean constraint
        carry_free_det="1-z-z^2",
        carry_free_traces=_carry_free_traces_golden_mean(n_max_primitive),
    )

    return [spec9, spec13, spec21]


def _make_table(rows: List[Dict[str, Any]]) -> str:
    lines: List[str] = []
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\small")
    lines.append(r"\setlength{\tabcolsep}{6pt}")
    lines.append(r"\renewcommand{\arraystretch}{1.15}")
    lines.append(
        r"\caption{并行核的单流在线编译（BFS）与 carry-free 指纹（由脚本 \texttt{scripts/exp\_parallel\_addition\_kernels\_bfs.py} 生成）。}"
    )
    lines.append(r"\label{tab:parallel-addition-kernels-bfs}")
    lines.append(r"\begin{tabular}{@{}lccccccc@{}}")
    lines.append(r"\toprule")
    lines.append(
        r"核（单流） & 输入字母表 $B$ & $|Q|$ & $\kappa$-均值 & $P(q^A\neq 0),P(q^B\neq 0)$ & carry-free $\det(I-zA_0)$ & $(p_n(A_0))_{n\le 12}$ & $\lambda(u)$: $u=0,1$ \\"
    )
    lines.append(r"\midrule")
    for r in rows:
        lines.append(
            " & ".join(
                [
                    r["name_tex"],
                    r["B_tex"],
                    str(r["states"]),
                    r["kappa_mean"],
                    r["qsplit"],
                    f"${r['det0']}$",
                    f"${r['p12']}$",
                    f"${r['lambda_u01']}$",
                ]
            )
            + r" \\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    return "\n".join(lines) + "\n"


def _make_fingerprint_table(rows: List[Dict[str, Any]], *, label: str) -> str:
    lines: List[str] = []
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\scriptsize")
    lines.append(r"\setlength{\tabcolsep}{5pt}")
    lines.append(r"\renewcommand{\arraystretch}{1.15}")
    lines.append(
        r"\caption{并行核指纹：由单流在线机组装到全局块级在线机（张量积），并给出 carry-free 骨架与最省力的 primitive 接口。}"
    )
    lines.append(rf"\label{{{label}}}")
    lines.append(r"\resizebox{\textwidth}{!}{%")
    lines.append(r"\begin{tabular}{@{}lccccccccc@{}}")
    lines.append(r"\toprule")
    lines.append(
        r"核 & 块宽 $m$ & 单流 $|Q|$ & 全局 $|Q|$ & $\delta$（digits） & $\mathbb{E}[\kappa]$（单/全） & $A_0$ det（单/全） & $(p_n(A_0))_{n\le 8}$（单/全） & $\lambda(0)$（单/全） & $\lambda(1)$（单/全） \\"
    )
    lines.append(r"\midrule")
    for r in rows:
        lines.append(
            " & ".join(
                [
                    r["name_tex"],
                    str(r["block_size"]),
                    str(r["states_flow"]),
                    str(r["states_glob"]),
                    str(r["delay_digits"]),
                    r["kappa_mean_pair"],
                    f"${r['det_pair']}$",
                    f"${r['p8_pair']}$",
                    f"${r['lambda0_pair']}$",
                    f"${r['lambda1_pair']}$",
                ]
            )
            + r" \\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"}")
    lines.append(r"\end{table}")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description="BFS compile 9/13/21-local kernels (single-flow)")
    parser.add_argument("--u-grid", type=str, default="0,0.25,0.5,0.75,1", help="Comma-separated u values")
    parser.add_argument("--primitive-n", type=int, default=12, help="Max n for carry-free primitive spectrum")
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs")
    args = parser.parse_args()

    u_grid = [float(x.strip()) for x in args.u_grid.split(",") if x.strip()]
    if not u_grid:
        raise SystemExit("Empty --u-grid")

    prog = Progress(label="par-add-kernels-bfs", every_seconds=20.0)
    print("[par-add-kernels-bfs] start", flush=True)

    specs = _make_specs(args.primitive_n)
    payload: Dict[str, Any] = {"u_grid": u_grid, "kernels": []}
    table_rows: List[Dict[str, Any]] = []
    fp_rows: List[Dict[str, Any]] = []

    for spec in specs:
        prog.tick(f"{spec.name} begin")
        idx, edges = _bfs_states(spec, prog)
        n_states = len(idx)
        b = len(spec.alphabet)

        # Convert edges to compact numeric arrays once (used by multiple computations).
        e_arr = np.asarray([(i, j, kA, kB) for (i, j, _a, kA, kB) in edges], dtype=np.int64)
        src = e_arr[:, 0]
        dst = e_arr[:, 1]
        kA = e_arr[:, 2]
        kB = e_arr[:, 3]
        kappa = kA + kB

        pi_np = _stationary_uniform_inputs_from_arrays(
            n_states=n_states, src=src, dst=dst, b=b, prog=prog, label=spec.name
        )
        pi = [float(x) for x in pi_np.tolist()]

        kdist = _kappa_dist_from_arrays(src=src, kappa=kappa, pi=pi_np, b=b)
        kmean = sum(k * p for k, p in kdist.items())
        pA, pB = _kappa_split_probs_from_arrays(src=src, kA=kA, kB=kB, pi=pi_np, b=b)

        # spectral radius of weighted adjacency for u grid
        lams = {}
        for u in u_grid:
            lams[str(u)] = _lambda_u_from_arrays(
                n_states=n_states, src=src, dst=dst, kappa=kappa, u=u, prog=prog, label=spec.name
            )
        lam0 = lams.get("0.0", lams.get("0", None))
        lam1 = lams.get("1.0", lams.get("1", None))

        # carry-free primitive spectrum from closed-form traces
        traces0 = spec.carry_free_traces
        p0 = _primitive_from_traces(traces0)

        # global assembly (block-level): m independent congruence streams
        m = spec.block_size
        states_glob = int(n_states**m)
        kappa_mean_glob = m * kmean
        # carry-free traces and primitives for global: product SFT => traces^m
        traces0_glob = [int(t**m) for t in traces0]
        p0_glob = _primitive_from_traces(traces0_glob)
        if spec.carry_free_det == "1-7z":
            det0_glob = "1-2401z"
        elif spec.carry_free_det == "1-3z":
            det0_glob = "1-9z"
        elif spec.carry_free_det == "1-z-z^2":
            det0_glob = "(1+z)^2(1-3z+z^2)"
        else:
            det0_glob = r"\det(I-z(A_0\otimes\cdots\otimes A_0))"

        payload["kernels"].append(
            {
                "name": spec.name,
                "block_size": spec.block_size,
                "alphabet_B": spec.alphabet,
                "states_reachable": n_states,
                # Deterministic single-flow transition edges (compact, for reproducible downstream diagnostics).
                # Format: [src, dst, kappa_A, kappa_B]. Total activity is kappa = kappa_A + kappa_B.
                "edges": [[int(i), int(j), int(kA), int(kB)] for (i, j, _a, kA, kB) in edges],
                "kappa_dist_uniform_inputs": kdist,
                "kappa_mean_uniform_inputs": kmean,
                "kappa_phase_probs_uniform_inputs": {"A": pA, "B": pB},
                "carry_free": {
                    "symbols": spec.carry_free_symbols,
                    "det_I_minus_zA0": spec.carry_free_det,
                    "traces_a_n": traces0,
                    "primitive_p_n": p0,
                },
                "global": {
                    "states_reachable": states_glob,
                    "kappa_mean_uniform_inputs": kappa_mean_glob,
                    "carry_free": {
                        "det_I_minus_zA0": det0_glob,
                        "traces_a_n": traces0_glob,
                        "primitive_p_n": p0_glob,
                    },
                },
                "lambda_u": lams,
            }
        )

        # Prepare LaTeX row.
        B_tex = (
            r"$\{-10,\dots,10\}$"
            if spec.alphabet[0] == -10
            else (r"$\{-6,\dots,6\}$" if spec.alphabet[0] == -6 else r"$\{-2,\dots,2\}$")
        )
        p12 = "(" + ",".join(str(x) for x in p0[:12]) + ")"
        name_tex = (
            r"$K_{9}$"
            if "9-local" in spec.name
            else (r"$K_{13}$" if "13-local" in spec.name else r"$K_{21}$")
        )
        table_rows.append(
            {
                "name_tex": name_tex,
                "B_tex": B_tex,
                "states": n_states,
                "kappa_mean": _fmt(kmean, 8),
                "qsplit": (f"{_fmt(pA,8)},{_fmt(pB,8)}" if "21-local" in spec.name else r"--"),
                "det0": spec.carry_free_det.replace("z", "z"),
                "p12": p12,
                "lambda_u01": f"{_fmt(lam0 or 0.0, 8)},{_fmt(lam1 or 0.0, 8)}",
            }
        )

        # fingerprint table row (flow vs global)
        delay_digits = spec.block_size * (1 if "9-local" in spec.name else (3 if "13-local" in spec.name else 5))
        p8_flow = "(" + ",".join(str(x) for x in p0[:8]) + ")"
        p8_glob = "(" + ",".join(str(x) for x in p0_glob[:8]) + ")"
        fp_rows.append(
            {
                "name_tex": name_tex,
                "block_size": spec.block_size,
                "states_flow": n_states,
                "states_glob": states_glob,
                "delay_digits": delay_digits,
                "kappa_mean_pair": f"{_fmt(kmean,8)}/{_fmt(kappa_mean_glob,8)}",
                "det_pair": f"{spec.carry_free_det}/{det0_glob}",
                "p8_pair": f"{p8_flow}/{p8_glob}",
                "lambda0_pair": f"{_fmt(lam0 or 0.0,8)}/{_fmt((lam0 or 0.0)**m,8)}",
                "lambda1_pair": f"{_fmt(lam1 or 0.0,8)}/{_fmt((lam1 or 0.0)**m,8)}",
            }
        )

        prog.tick(f"{spec.name} done states={n_states}")

    if not args.no_output:
        out_json = export_dir() / "parallel_addition_kernels_bfs.json"
        _write_text(out_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"[par-add-kernels-bfs] wrote {out_json}", flush=True)

        out_tex = generated_dir() / "tab_parallel_addition_kernels_bfs.tex"
        _write_text(out_tex, _make_table(table_rows))
        print(f"[par-add-kernels-bfs] wrote {out_tex}", flush=True)

        out_fp = generated_dir() / "tab_parallel_addition_kernels_fingerprint.tex"
        _write_text(out_fp, _make_fingerprint_table(fp_rows, label="tab:parallel-addition-kernels-fingerprint"))
        print(f"[par-add-kernels-bfs] wrote {out_fp}", flush=True)

        out_fp_main = generated_dir() / "tab_parallel_addition_kernels_fingerprint_main.tex"
        _write_text(out_fp_main, _make_fingerprint_table(fp_rows, label="tab:parallel-addition-kernels-fingerprint-main"))
        print(f"[par-add-kernels-bfs] wrote {out_fp_main}", flush=True)

    print("[par-add-kernels-bfs] done", flush=True)


if __name__ == "__main__":
    main()

