#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Exact sync-time statistics for the real-input kernel via an absorbing Markov chain.

We study the 10-state sync kernel (deterministic automaton on Q with input alphabet {0,1,2})
driven by *real arithmetic inputs* coming from two independent Zeckendorf (golden-mean) shifts:
  x,y ∈ {0,1}^Z with forbidden word 11, and d_t = x_t + y_t ∈ {0,1,2}.

Observer model:
- inputs (x_t,y_t) are observed,
- the initial internal kernel state is unknown (a subset of Q),
- the memory m_t=(x_{t-1},y_{t-1}) is tracked (4 states).

The belief-state dynamics is a Markov chain on (subset_mask, memory_state) where
subset_mask evolves deterministically by d_t, and memory_state evolves by the Parry
(max-entropy) Markov chain on X×X. Synchronization occurs when subset_mask is a singleton
(absorbing).

We compute, in exact Q(sqrt(5)) arithmetic:
- E[τ] and Var(τ) for two initial conditions:
    (A) worst-case: subset_mask = Q (all 10 states), memory distributed as Parry stationary;
    (B) essential: subset_mask restricted to the essential 20-state core by memory class,
        memory distributed as Parry stationary.
- The transient spectral radius ρ (numeric), and identify it as 1/φ when applicable.
- Quantiles of τ from the full distribution computed numerically on the transient chain.

Outputs (default):
- artifacts/export/real_input_40_sync_time_absorbing_chain.json
- sections/generated/tab_real_input_40_sync_time_absorbing_chain.tex
"""

from __future__ import annotations

import argparse
import json
import math
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from exp_sync_kernel_real_input_40 import KERNEL_STATES, build_kernel_edges


# ---- Q(sqrt(5)) exact arithmetic ----

Q5 = Tuple[Fraction, Fraction]  # a + b*sqrt(5)


def q5(a: int | Fraction = 0, b: int | Fraction = 0) -> Q5:
    return (a if isinstance(a, Fraction) else Fraction(a), b if isinstance(b, Fraction) else Fraction(b))


def q5_is_zero(x: Q5) -> bool:
    return x[0] == 0 and x[1] == 0


def q5_add(x: Q5, y: Q5) -> Q5:
    return (x[0] + y[0], x[1] + y[1])


def q5_sub(x: Q5, y: Q5) -> Q5:
    return (x[0] - y[0], x[1] - y[1])


def q5_neg(x: Q5) -> Q5:
    return (-x[0], -x[1])


def q5_mul(x: Q5, y: Q5) -> Q5:
    # (a+b s)(c+d s) = (ac+5bd) + (ad+bc) s
    a, b = x
    c, d = y
    return (a * c + Fraction(5) * b * d, a * d + b * c)


def q5_inv(x: Q5) -> Q5:
    a, b = x
    den = a * a - Fraction(5) * b * b
    if den == 0:
        raise ZeroDivisionError("singular Q(sqrt5) element")
    return (a / den, -b / den)


def q5_div(x: Q5, y: Q5) -> Q5:
    return q5_mul(x, q5_inv(y))


def q5_float(x: Q5) -> float:
    return float(x[0]) + float(x[1]) * math.sqrt(5.0)


def _tex_frac(f: Fraction) -> str:
    if f.denominator == 1:
        return str(f.numerator)
    return rf"\frac{{{f.numerator}}}{{{f.denominator}}}"


def tex_q5(x: Q5) -> str:
    a, b = x
    if b == 0:
        return _tex_frac(a)
    # a + b sqrt(5)
    sgn = "+" if b > 0 else "-"
    bb = b if b > 0 else -b
    if a == 0:
        if sgn == "-":
            return rf"-{_tex_frac(bb)}\sqrt5"
        return rf"{_tex_frac(bb)}\sqrt5"
    return rf"{_tex_frac(a)} {sgn} {_tex_frac(bb)}\sqrt5"


# ---- Kernel delta and subset evolution ----


def build_delta_Q() -> Tuple[List[str], Dict[Tuple[str, int], str]]:
    edges = build_kernel_edges()
    Q = list(KERNEL_STATES)
    delta: Dict[Tuple[str, int], str] = {}
    for e in edges:
        key = (e.src, int(e.d))
        if key in delta:
            raise RuntimeError(f"non-deterministic transition at {key}")
        delta[key] = e.dst
    for s in Q:
        for d in (0, 1, 2):
            if (s, d) not in delta:
                raise RuntimeError(f"missing transition for {(s, d)}")
    return Q, delta


def step_mask(mask: int, d: int, *, Q: Sequence[str], idx: Dict[str, int], delta: Dict[Tuple[str, int], str]) -> int:
    mm = 0
    x = mask
    while x:
        lsb = x & -x
        i = lsb.bit_length() - 1
        s = Q[i]
        t = delta[(s, d)]
        mm |= 1 << idx[t]
        x -= lsb
    return mm


def is_singleton(mask: int) -> bool:
    return mask != 0 and (mask & (mask - 1)) == 0


# ---- Parry input-memory chain for X×X (exact) ----


def parry_bit_transition(prev: int, nxt: int) -> Q5:
    # Golden mean shift on bits with adjacency:
    #   0 -> 0,1
    #   1 -> 0
    # Under Parry: P(0->0)=1/phi, P(0->1)=1/phi^2, P(1->0)=1.
    if prev not in (0, 1) or nxt not in (0, 1):
        return q5(0)
    if prev == 1:
        return q5(1) if nxt == 0 else q5(0)
    # prev == 0
    invphi = q5(Fraction(-1, 2), Fraction(1, 2))       # (sqrt5 - 1)/2
    invphi2 = q5(Fraction(3, 2), Fraction(-1, 2))      # (3 - sqrt5)/2
    return invphi if nxt == 0 else invphi2


def parry_mem_transition(m: Tuple[int, int], mp: Tuple[int, int]) -> Q5:
    px, py = m
    x, y = mp
    return q5_mul(parry_bit_transition(px, x), parry_bit_transition(py, y))


def parry_bit_stationary(p: int) -> Q5:
    # π(0)=(5+sqrt5)/10, π(1)=(5-sqrt5)/10.
    if p == 0:
        return q5(Fraction(1, 2), Fraction(1, 10))
    if p == 1:
        return q5(Fraction(1, 2), Fraction(-1, 10))
    return q5(0)


def parry_mem_stationary(m: Tuple[int, int]) -> Q5:
    px, py = m
    return q5_mul(parry_bit_stationary(px), parry_bit_stationary(py))


def mem_states() -> List[Tuple[int, int]]:
    return [(0, 0), (0, 1), (1, 0), (1, 1)]


def mem_out_neighbors(m: Tuple[int, int]) -> List[Tuple[Tuple[int, int], int, Q5]]:
    # Return list of (mp, d, prob) for allowed next memory mp=(x,y),
    # where d=x+y and prob is Parry transition probability.
    px, py = m
    out: List[Tuple[Tuple[int, int], int, Q5]] = []
    for x in (0, 1):
        if px == 1 and x == 1:
            continue
        for y in (0, 1):
            if py == 1 and y == 1:
                continue
            mp = (x, y)
            d = int(x + y)
            p = parry_mem_transition(m, mp)
            if q5_is_zero(p):
                continue
            out.append((mp, d, p))
    # sanity: outgoing probs sum to 1
    s = q5(0)
    for _mp, _d, p in out:
        s = q5_add(s, p)
    if s != q5(1):
        raise RuntimeError(f"Parry transition row does not sum to 1 for m={m}: got {s}")
    return out


# ---- Absorbing chain build + exact moments ----


def gaussian_solve(A: List[List[Q5]], b: List[Q5]) -> List[Q5]:
    """Solve A x = b over Q(sqrt5) by Gauss-Jordan elimination (exact)."""
    n = len(A)
    M = [row[:] for row in A]
    x = b[:]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if not q5_is_zero(M[r][col]):
                piv = r
                break
        if piv is None:
            raise RuntimeError("singular system (no pivot)")
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            x[col], x[piv] = x[piv], x[col]

        inv_p = q5_inv(M[col][col])
        for j in range(col, n):
            M[col][j] = q5_mul(M[col][j], inv_p)
        x[col] = q5_mul(x[col], inv_p)

        for r in range(n):
            if r == col:
                continue
            f = M[r][col]
            if q5_is_zero(f):
                continue
            for j in range(col, n):
                M[r][j] = q5_sub(M[r][j], q5_mul(f, M[col][j]))
            x[r] = q5_sub(x[r], q5_mul(f, x[col]))
    return x


def build_transient_chain(
    *,
    initial_masks: Dict[Tuple[int, int], int],
    Q: List[str],
    delta: Dict[Tuple[str, int], str],
) -> Tuple[List[Tuple[int, Tuple[int, int]]], List[List[Q5]]]:
    """Return (transient_states, Qmat) where Qmat is transient->transient matrix."""
    nQ = len(Q)
    idx = {s: i for i, s in enumerate(Q)}
    start = [(mask, m) for m, mask in initial_masks.items()]

    seen: Dict[Tuple[int, Tuple[int, int]], int] = {}
    q = deque(start)
    while q:
        mask, m = q.popleft()
        if is_singleton(mask):
            continue
        key = (mask, m)
        if key in seen:
            continue
        seen[key] = len(seen)
        for mp, d, _p in mem_out_neighbors(m):
            mask2 = step_mask(mask, d, Q=Q, idx=idx, delta=delta)
            if is_singleton(mask2):
                continue
            q.append((mask2, mp))

    states = [None] * len(seen)  # type: ignore[list-item]
    for k, i in seen.items():
        states[i] = k
    states2: List[Tuple[int, Tuple[int, int]]] = [(mask, m) for (mask, m) in states]  # type: ignore[arg-type]

    n = len(states2)
    Qmat: List[List[Q5]] = [[q5(0) for _ in range(n)] for _ in range(n)]
    for i, (mask, m) in enumerate(states2):
        for mp, d, p in mem_out_neighbors(m):
            mask2 = step_mask(mask, d, Q=Q, idx=idx, delta=delta)
            if is_singleton(mask2):
                continue
            j = seen[(mask2, mp)]
            Qmat[i][j] = q5_add(Qmat[i][j], p)
    return states2, Qmat


def expected_and_var(
    *,
    transient_states: List[Tuple[int, Tuple[int, int]]],
    Qmat: List[List[Q5]],
    init_prob: Dict[Tuple[int, Tuple[int, int]], Q5],
) -> Tuple[Q5, Q5, List[Q5], List[Q5]]:
    n = len(transient_states)
    idx_state = {st: i for i, st in enumerate(transient_states)}

    # Build A = I - Q.
    A: List[List[Q5]] = [[q5(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            A[i][j] = q5_neg(Qmat[i][j])
        A[i][i] = q5_add(A[i][i], q5(1))

    ones = [q5(1) for _ in range(n)]
    t = gaussian_solve(A, ones)

    # rhs2 = 1 + 2 Q t
    rhs2: List[Q5] = [q5(1) for _ in range(n)]
    for i in range(n):
        s = q5(0)
        for j in range(n):
            if q5_is_zero(Qmat[i][j]):
                continue
            s = q5_add(s, q5_mul(Qmat[i][j], t[j]))
        rhs2[i] = q5_add(rhs2[i], q5_mul(q5(2), s))

    u = gaussian_solve(A, rhs2)

    # Aggregate over the initial distribution (supported on a few transient states).
    E = q5(0)
    E2 = q5(0)
    for st, p in init_prob.items():
        i = idx_state[st]
        E = q5_add(E, q5_mul(p, t[i]))
        E2 = q5_add(E2, q5_mul(p, u[i]))
    Var = q5_sub(E2, q5_mul(E, E))
    return E, Var, t, u


def _rho_and_quantiles(
    *,
    transient_states: List[Tuple[int, Tuple[int, int]]],
    Qmat: List[List[Q5]],
    init_prob: Dict[Tuple[int, Tuple[int, int]], Q5],
    q_list: Sequence[float],
    n_max: int,
) -> Tuple[float, Dict[float, int]]:
    n = len(transient_states)
    idx_state = {st: i for i, st in enumerate(transient_states)}

    Qf = np.zeros((n, n), dtype=float)
    for i in range(n):
        for j in range(n):
            if not q5_is_zero(Qmat[i][j]):
                Qf[i, j] = q5_float(Qmat[i][j])

    # Spectral radius on transient operator (numeric).
    eig = np.linalg.eigvals(Qf)
    rho = float(np.max(np.abs(eig))) if eig.size else 0.0

    # Survival recursion: v_{n+1} = v_n Q, survival(n)=sum(v_n)=P(τ>n).
    v = np.zeros(n, dtype=float)
    for st, p in init_prob.items():
        v[idx_state[st]] += q5_float(p)

    survival = float(np.sum(v))
    qs = sorted(float(q) for q in q_list)
    out: Dict[float, int] = {}
    for q in qs:
        out[q] = -1

    # n=0: P(τ<=0)=0
    for step in range(0, n_max + 1):
        cdf = 1.0 - float(survival)
        for q in qs:
            if out[q] == -1 and cdf >= q - 1e-15:
                out[q] = int(step)
        if all(out[q] != -1 for q in qs):
            break
        v = v @ Qf
        survival = float(np.sum(v))

    # Replace any remaining -1 with n_max.
    for q in qs:
        if out[q] == -1:
            out[q] = int(n_max)
    return rho, out


# ---- Export helpers ----


@dataclass(frozen=True)
class ScenarioResult:
    name: str
    n_transient: int
    E_qsqrt5: Tuple[str, str]
    Var_qsqrt5: Tuple[str, str]
    E_float: float
    Var_float: float
    rho_float: float
    rho_closed_form: str
    quantiles: Dict[str, int]


def _pair_str(x: Q5) -> Tuple[str, str]:
    return (str(x[0]), str(x[1]))


def _rho_closed_form(rho: float) -> str:
    # Identify rho as 1/phi = (sqrt5-1)/2 if it matches numerically.
    cand = (math.sqrt(5.0) - 1.0) / 2.0
    if math.isfinite(rho) and abs(rho - cand) <= 5e-13:
        return r"\varphi^{-1}"
    return f"{rho:.15g}"


def write_tex_table(path: Path, rows: List[ScenarioResult]) -> None:
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_real_input_40_sync_time_absorbing_chain.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.15}")
    lines.append(
        "\\caption{随机真实输入（Parry 最大熵测度）下达到同步的等待时间统计。"
        "设 $\\tau$ 为子集-记忆吸收链的吸收时间（同步时刻），表中给出两种初始不确定性："
        "(i) worst：初始子集为 $Q$；(ii) essential：初始子集按命题~\\ref{prop:real-input-40-essential-20} 的 $20$ 状态核心对记忆类做约束。}"
    )
    lines.append("\\label{tab:real-input-40-sync-time-absorbing-chain}")
    lines.append("\\begin{tabular}{l r l l l r r r}")
    lines.append("\\toprule")
    lines.append("scenario & $n_{\\mathrm{tr}}$ & $\\mathbb{E}[\\tau]$ & $\\mathrm{Var}(\\tau)$ & $\\rho$ & $q_{0.05}$ & $q_{0.50}$ & $q_{0.95}$\\\\")
    lines.append("\\midrule")
    for r in rows:
        q05 = int(r.quantiles.get("0.05", -1))
        q50 = int(r.quantiles.get("0.5", -1))
        q95 = int(r.quantiles.get("0.95", -1))
        lines.append(
            f"{r.name}"
            f" & {int(r.n_transient)}"
            f" & ${tex_q5((Fraction(r.E_qsqrt5[0]), Fraction(r.E_qsqrt5[1])))}$"
            f" & ${tex_q5((Fraction(r.Var_qsqrt5[0]), Fraction(r.Var_qsqrt5[1])))}$"
            f" & ${r.rho_closed_form}$"
            f" & {q05} & {q50} & {q95}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Exact sync-time stats via absorbing chain (real-input kernel).")
    parser.add_argument("--n-max", type=int, default=120, help="Max steps for quantile search (numeric recursion)")
    args = parser.parse_args()

    Q, delta = build_delta_Q()
    nQ = len(Q)
    full_mask = (1 << nQ) - 1

    mems = mem_states()

    # Initial memory distribution (Parry stationary).
    pi_mem = {m: parry_mem_stationary(m) for m in mems}
    # sanity: sums to 1
    s_pi = q5(0)
    for v in pi_mem.values():
        s_pi = q5_add(s_pi, v)
    if s_pi != q5(1):
        raise RuntimeError(f"memory stationary distribution does not sum to 1: {s_pi}")

    # Scenario A: worst-case subset = Q for each memory.
    init_masks_worst = {m: full_mask for m in mems}

    # Scenario B: essential-core subset by memory class (Prop. real-input-40-essential-20).
    idxQ = {s: i for i, s in enumerate(Q)}

    def mask_of(states: Iterable[str]) -> int:
        mm = 0
        for s in states:
            if s not in idxQ:
                raise RuntimeError(f"unknown kernel state in mask: {s}")
            mm |= 1 << idxQ[s]
        return mm

    init_masks_ess = {
        (0, 0): mask_of(["000", "001", "010", "100", "01-1", "11-1"]),
        (0, 1): mask_of(["000", "001", "002", "100", "101"]),
        (1, 0): mask_of(["000", "001", "002", "100", "101"]),
        (1, 1): mask_of(["0-12", "1-12", "002", "101"]),
    }

    scenarios: List[Tuple[str, Dict[Tuple[int, int], int]]] = [
        ("worst", init_masks_worst),
        ("essential", init_masks_ess),
    ]

    results: List[ScenarioResult] = []
    payload: Dict[str, object] = {
        "model": "real_input_40_sync_time_absorbing_chain",
        "memory_stationary_qsqrt5": {f"{m[0]}{m[1]}": _pair_str(pi_mem[m]) for m in mems},
        "scenarios": {},
    }

    for name, init_masks in scenarios:
        transient_states, Qmat = build_transient_chain(initial_masks=init_masks, Q=Q, delta=delta)
        init_prob = {(init_masks[m], m): pi_mem[m] for m in mems}
        E, Var, _t, _u = expected_and_var(transient_states=transient_states, Qmat=Qmat, init_prob=init_prob)

        rho, qs = _rho_and_quantiles(
            transient_states=transient_states,
            Qmat=Qmat,
            init_prob=init_prob,
            q_list=[0.05, 0.5, 0.95],
            n_max=int(args.n_max),
        )

        res = ScenarioResult(
            name=name,
            n_transient=int(len(transient_states)),
            E_qsqrt5=_pair_str(E),
            Var_qsqrt5=_pair_str(Var),
            E_float=float(q5_float(E)),
            Var_float=float(q5_float(Var)),
            rho_float=float(rho),
            rho_closed_form=_rho_closed_form(rho),
            quantiles={str(k): int(v) for k, v in qs.items()},
        )
        results.append(res)

        payload["scenarios"][name] = {
            "n_transient": int(len(transient_states)),
            "E_qsqrt5": _pair_str(E),
            "Var_qsqrt5": _pair_str(Var),
            "E_float": float(q5_float(E)),
            "Var_float": float(q5_float(Var)),
            "rho_float": float(rho),
            "rho_closed_form": res.rho_closed_form,
            "quantiles": {str(k): int(v) for k, v in qs.items()},
        }

    jout = export_dir() / "real_input_40_sync_time_absorbing_chain.json"
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    tout = generated_dir() / "tab_real_input_40_sync_time_absorbing_chain.tex"
    write_tex_table(tout, rows=results)

    for r in results:
        print(
            f"[sync-time] {r.name}: n_tr={r.n_transient} E~{r.E_float:.12g} Var~{r.Var_float:.12g} rho~{r.rho_float:.12g}",
            flush=True,
        )
    print(f"[sync-time] wrote {jout} and {tout}", flush=True)


if __name__ == "__main__":
    main()

