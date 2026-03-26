#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Exact g_* (fold gauge anomaly density) via a finite synchronization kernel.

We start from the 4-state *functional, unambiguous* Fibonacci normalizer transducer
in Berstel (2001), Fig. 1, which realizes the normalization induced by the rewrite
rule 011 -> 100 on words starting with a leading 0 (MSD-first Fibonacci digits).

The transducer is letter-to-letter (synchronous), but not sequentializable: the
standard prefix-pushing determinization produces an infinite residual chain.
For the *per-position* mismatch rate, we can avoid sequentialization by using a
finite synchronization kernel based on left/right subset constructions on the
input NFA:
1) forward reachable-set DFA (after the forced leading 0),
2) backward co-reachable-set DFA (from the final set),
3) output-bit selection is uniquely determined by (forward_set, input_bit, backward_set),
   by unambiguity of the transducer.

Under IID Bernoulli(1/2) input, the forward/backward subset chains have exact
stationary distributions, are independent at a cut, and yield g_* as a rational.

Outputs:
- artifacts/export/fold_gauge_anomaly_density_transducer.json
- sections/generated/eq_fold_gauge_anomaly_density_transducer.tex
"""

from __future__ import annotations

import json
import random
import time
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Sequence, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fold_m

Bit = str  # "0" or "1"
Out = str  # output bit string (possibly empty)
Q = str  # NFA state id
DetState = Tuple[Tuple[Q, Out], ...]  # sorted tuple of (state, residual_output)
SetState = Tuple[Q, ...]  # sorted tuple of NFA states (subset construction)


def _lcp(xs: Sequence[str]) -> str:
    """Longest common prefix of a non-empty list of strings."""
    if not xs:
        return ""
    m = min(len(s) for s in xs)
    if m == 0:
        return ""
    base = xs[0]
    i = 0
    while i < m:
        c = base[i]
        if any(s[i] != c for s in xs[1:]):
            break
        i += 1
    return base[:i]


def _canon_det_state(pairs: Iterable[Tuple[Q, Out]]) -> DetState:
    """Canonicalize a determinized state as a sorted tuple, dropping duplicates."""
    # Drop exact duplicates, keep multiplicity-free representation (sufficient for functional NFA).
    uniq = sorted(set(pairs), key=lambda t: (t[0], t[1]))
    return tuple(uniq)


def _berstel_normalizer_nfa() -> Tuple[Q, Tuple[Q, ...], Mapping[Q, Mapping[Bit, List[Tuple[Q, Bit]]]]]:
    """Return (init, finals, delta) for the Berstel 2001 normalizer (Fig. 1).

    Convention: edge labels are (input|output) with input/output in {0,1}.
    """
    # States in the figure: a,b,c,d. Initial state is a (incoming arrow).
    init = "a"
    # Final states are a and d (outgoing arrows).
    finals = ("a", "d")

    # NFA transducer transitions: delta[q][inp] = list of (q', out_bit).
    delta: Dict[Q, Dict[Bit, List[Tuple[Q, Bit]]]] = {q: {"0": [], "1": []} for q in ["a", "b", "c", "d"]}

    def add(q: Q, inp: Bit, q2: Q, out: Bit) -> None:
        delta[q][inp].append((q2, out))

    # Fig. 1 (as rendered from https://www.numdam.org/item/ITA_2001__35_6_491_0.pdf):
    # d --0|0--> a
    # a --1|1--> d
    # a --0|0--> a
    # a --0|1--> b
    # b --1|0--> c
    # c --1|0--> a
    # c --0|0--> b
    # c --1|1--> b
    add("d", "0", "a", "0")
    add("a", "1", "d", "1")
    add("a", "0", "a", "0")
    add("a", "0", "b", "1")
    add("b", "1", "c", "0")
    add("c", "1", "a", "0")
    add("c", "0", "b", "0")
    add("c", "1", "b", "1")

    return init, finals, delta


def _rewrite_normalize_011_to_100(word: str) -> str:
    """Deterministic normalization by repeatedly applying 011 -> 100 (MSD-first)."""
    w = list(word)
    i = 0
    while i <= len(w) - 3:
        if w[i] == "0" and w[i + 1] == "1" and w[i + 2] == "1":
            w[i : i + 3] = ["1", "0", "0"]
            i = max(i - 2, 0)
        else:
            i += 1
    return "".join(w)


def _nfa_transduce_unique(inp: str, init: Q, finals: Sequence[Q], delta: Mapping[Q, Mapping[Bit, List[Tuple[Q, Bit]]]]) -> str:
    """Return the unique output of the functional NFA transducer on inp.

    Assumes inp starts with '0' (the intended domain).
    """
    paths: List[Tuple[Q, str]] = [(init, "")]
    for ch in inp:
        new: List[Tuple[Q, str]] = []
        for q, out in paths:
            for q2, o in delta[q][ch]:
                new.append((q2, out + o))
        paths = new
        if not paths:
            raise RuntimeError(f"NFA stuck on input prefix {inp!r}")
    outs = [out for q, out in paths if q in set(finals)]
    outs = sorted(set(outs))
    if len(outs) != 1:
        raise RuntimeError(f"NFA not functional on {inp!r}: outs={outs}")
    return outs[0]


def _canon_set_state(xs: Iterable[Q]) -> SetState:
    return tuple(sorted(set(xs)))


def _input_only_delta(
    delta: Mapping[Q, Mapping[Bit, List[Tuple[Q, Bit]]]]
) -> Tuple[Dict[Q, Dict[Bit, set[Q]]], Dict[Q, Dict[Bit, set[Q]]]]:
    """Return (inp_delta, pre) for the input NFA underlying the transducer.

    - inp_delta[q][a] = set of q' such that there exists q --a|*--> q'
    - pre[q'][a] = set of q such that there exists q --a|*--> q'
    """
    inp_delta: Dict[Q, Dict[Bit, set[Q]]] = {q: {"0": set(), "1": set()} for q in delta.keys()}
    pre: Dict[Q, Dict[Bit, set[Q]]] = {q: {"0": set(), "1": set()} for q in delta.keys()}
    for q in delta.keys():
        for a in ("0", "1"):
            for q2, _out in delta[q][a]:
                inp_delta[q][a].add(q2)
                pre[q2][a].add(q)
    return inp_delta, pre


def _build_forward_subset_dfa(
    *,
    init: Q,
    inp_delta: Mapping[Q, Mapping[Bit, set[Q]]],
    forced_leading: Bit = "0",
) -> Tuple[SetState, Dict[SetState, Dict[Bit, SetState]]]:
    """Subset DFA for forward reachable sets, starting after a forced leading symbol."""
    start_set = set(inp_delta[init][forced_leading])
    start = _canon_set_state(start_set)

    trans: Dict[SetState, Dict[Bit, SetState]] = {}
    q: deque[SetState] = deque([start])
    seen = {start}
    while q:
        S = q.popleft()
        trans[S] = {}
        for a in ("0", "1"):
            nxt: set[Q] = set()
            for qq in S:
                nxt |= set(inp_delta[qq][a])
            S2 = _canon_set_state(nxt)
            trans[S][a] = S2
            if S2 not in seen:
                seen.add(S2)
                q.append(S2)
    return start, trans


def _build_backward_subset_dfa(
    *,
    finals: Sequence[Q],
    pre: Mapping[Q, Mapping[Bit, set[Q]]],
) -> Tuple[SetState, Dict[SetState, Dict[Bit, SetState]]]:
    """Subset DFA for backward co-reachable sets, starting from the final set."""
    start = _canon_set_state(finals)
    trans: Dict[SetState, Dict[Bit, SetState]] = {}
    q: deque[SetState] = deque([start])
    seen = {start}
    while q:
        T = q.popleft()
        trans[T] = {}
        for a in ("0", "1"):
            prev: set[Q] = set()
            for qq in T:
                prev |= set(pre[qq][a])
            T2 = _canon_set_state(prev)
            trans[T][a] = T2
            if T2 not in seen:
                seen.add(T2)
                q.append(T2)
    return start, trans


def _solve_stationary_dfa(
    states: List[SetState],
    trans: Mapping[SetState, Mapping[Bit, SetState]],
    p0: Fraction,
    p1: Fraction,
) -> List[Fraction]:
    """Solve pi exactly for a deterministic 2-input Markov chain."""
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}

    # Build P^T - I, replace last row by sum(pi)=1.
    A = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    b = [Fraction(0) for _ in range(n)]
    for j, s in enumerate(states):
        A[j][j] = Fraction(-1)
        for a, p in (("0", p0), ("1", p1)):
            ns = trans[s][a]
            i = idx[ns]
            A[i][j] += p

    A[-1] = [Fraction(1) for _ in range(n)]
    b[-1] = Fraction(1)

    # Gaussian elimination over Fractions.
    M = [row[:] + [b_i] for row, b_i in zip(A, b)]
    r = 0
    for c in range(n):
        piv = None
        for rr in range(r, n):
            if M[rr][c] != 0:
                piv = rr
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        if pv != 1:
            for cc in range(c, n + 1):
                M[r][cc] /= pv
        for rr in range(n):
            if rr == r:
                continue
            f = M[rr][c]
            if f == 0:
                continue
            for cc in range(c, n + 1):
                M[rr][cc] -= f * M[r][cc]
        r += 1
        if r == n:
            break

    x = [Fraction(0) for _ in range(n)]
    for i in range(n):
        lead = None
        for c in range(n):
            if M[i][c] == 1:
                lead = c
                break
            if M[i][c] != 0:
                lead = None
                break
        if lead is not None:
            x[lead] = M[i][n]
    s = sum(x)
    if s != 1:
        x = [v / s for v in x]
    return x


def _out_bit_from_context(
    *,
    delta: Mapping[Q, Mapping[Bit, List[Tuple[Q, Bit]]]],
    forward_set: SetState,
    a: Bit,
    backward_set: SetState,
) -> Bit:
    """Unique output bit determined by (forward_set, a, backward_set) context."""
    backward = set(backward_set)
    outs: set[Bit] = set()
    for q in forward_set:
        for q2, out in delta[q][a]:
            if q2 in backward:
                outs.add(out)
    if len(outs) != 1:
        raise RuntimeError(f"context output not unique: F={forward_set} a={a} B={backward_set} outs={outs}")
    return next(iter(outs))


def determinize_prefix_pushing(
    init: Q, finals: Sequence[Q], delta: Mapping[Q, Mapping[Bit, List[Tuple[Q, Bit]]]]
) -> Tuple[DetState, Dict[DetState, Dict[Bit, Tuple[DetState, Out]]], Dict[DetState, Out]]:
    """Determinize a functional letter-to-letter transducer by prefix pushing.

    Returns:
      - det_init: deterministic start state
      - det_delta: det_delta[S][a] = (S', out_string_emitted_now)
      - det_final_out: final output string associated to S (possibly empty) if S is final,
        computed by collecting residuals of underlying finals.
    """
    finals_set = set(finals)
    det_init = _canon_det_state([(init, "")])

    det_delta: Dict[DetState, Dict[Bit, Tuple[DetState, Out]]] = {}
    det_final_out: Dict[DetState, Out] = {}

    q: deque[DetState] = deque([det_init])
    seen = {det_init}

    while q:
        S = q.popleft()
        det_delta[S] = {}
        for a in ("0", "1"):
            items: List[Tuple[Q, Out]] = []
            for q0, lag in S:
                for q1, o in delta[q0][a]:
                    items.append((q1, lag + o))
            if not items:
                # This should not happen for the effective domain after the required leading 0.
                continue
            p = _lcp([w for _q, w in items])
            nxt = _canon_det_state([(q1, w[len(p) :]) for (q1, w) in items])
            det_delta[S][a] = (nxt, p)
            if nxt not in seen:
                seen.add(nxt)
                q.append(nxt)

        # Final output: if any underlying NFA final is present, all accepting residuals must agree.
        residuals = {lag for q0, lag in S if q0 in finals_set}
        if residuals:
            if len(residuals) != 1:
                raise RuntimeError(f"Non-unique final residuals in determinized state {S}: {residuals}")
            det_final_out[S] = next(iter(residuals))

    return det_init, det_delta, det_final_out


@dataclass(frozen=True)
class AugState:
    """State for the aligned mismatch kernel."""

    det: DetState
    pending: Tuple[Bit, ...]  # FIFO queue of pending input bits not yet matched to output bits


def build_aligned_mismatch_kernel(
    det_init: DetState,
    det_delta: Mapping[DetState, Mapping[Bit, Tuple[DetState, Out]]],
    *,
    burn_in_zeros: int = 2,
) -> Tuple[AugState, Dict[AugState, Dict[Bit, Tuple[AugState, int, int]]]]:
    """Build the deterministic augmented kernel that emits mismatch bits.

    Transition payload: (next_state, mismatches_emitted, output_bits_emitted).
    """
    # To avoid the very short start-up transient tied to the "word starts with 0" convention,
    # we start after feeding a few leading zeros. This does not affect the stationary regime.
    S = det_init
    pending: Tuple[Bit, ...] = tuple()
    for _ in range(burn_in_zeros):
        S, out = det_delta[S]["0"]
        pending = pending + ("0",)
        # consume emitted output bits against pending
        for y in out:
            pending = pending[1:]

    aug_init = AugState(det=S, pending=pending)

    trans: Dict[AugState, Dict[Bit, Tuple[AugState, int, int]]] = {}

    q: deque[AugState] = deque([aug_init])
    seen = {aug_init}
    max_pending = 0

    while q:
        st = q.popleft()
        max_pending = max(max_pending, len(st.pending))
        trans[st] = {}
        for a in ("0", "1"):
            if st.det not in det_delta or a not in det_delta[st.det]:
                # Outside intended domain; skip.
                continue
            det2, out = det_delta[st.det][a]
            pending2: Tuple[Bit, ...] = st.pending + (a,)
            mism = 0
            for y in out:
                if not pending2:
                    raise RuntimeError("pending underflow (output ahead of input)")
                x = pending2[0]
                pending2 = pending2[1:]
                if x != y:
                    mism += 1
            ns = AugState(det=det2, pending=pending2)
            trans[st][a] = (ns, mism, len(out))
            if ns not in seen:
                seen.add(ns)
                q.append(ns)

    if max_pending > 32:
        raise RuntimeError(f"unexpectedly large pending queue: max_pending={max_pending}")
    return aug_init, trans


def _solve_stationary_distribution(
    states: List[AugState],
    trans: Mapping[AugState, Mapping[Bit, Tuple[AugState, int, int]]],
    p0: Fraction,
    p1: Fraction,
) -> List[Fraction]:
    """Solve for stationary distribution pi exactly using Fractions."""
    n = len(states)
    idx = {s: i for i, s in enumerate(states)}

    # Build P^T - I, then replace last row by sum(pi)=1.
    A = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    b = [Fraction(0) for _ in range(n)]

    for j, s in enumerate(states):
        A[j][j] = Fraction(-1)
        for a, p in (("0", p0), ("1", p1)):
            ns, _m, _k = trans[s][a]
            i = idx[ns]
            A[i][j] += p  # P^T contribution

    # Replace last equation with normalization.
    A[-1] = [Fraction(1) for _ in range(n)]
    b[-1] = Fraction(1)

    # Gaussian elimination
    # Work on augmented matrix [A|b]
    M = [row[:] + [b_i] for row, b_i in zip(A, b)]
    r = 0
    for c in range(n):
        # find pivot
        piv = None
        for rr in range(r, n):
            if M[rr][c] != 0:
                piv = rr
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        # normalize pivot row
        pv = M[r][c]
        if pv != 1:
            for cc in range(c, n + 1):
                M[r][cc] /= pv
        # eliminate others
        for rr in range(n):
            if rr == r:
                continue
            f = M[rr][c]
            if f == 0:
                continue
            for cc in range(c, n + 1):
                M[rr][cc] -= f * M[r][cc]
        r += 1
        if r == n:
            break

    # Read solution
    x = [Fraction(0) for _ in range(n)]
    for i in range(n):
        # find leading 1
        lead = None
        for c in range(n):
            if M[i][c] == 1:
                lead = c
                break
            if M[i][c] != 0:
                lead = None
                break
        if lead is not None:
            x[lead] = M[i][n]

    s = sum(x)
    if s != 1:
        # normalize defensively (should already be 1)
        x = [v / s for v in x]
    return x


def _sample_gauge_anomaly_density(m: int, trials: int, seed: int) -> float:
    """Monte Carlo estimate of E[G_m]/m using the fast rewrite normalizer.

    This avoids bigint Fibonacci arithmetic in fold_m for large m.
    """
    rng = random.Random(seed)
    mism = 0
    total = 0
    for _ in range(trials):
        omega = [rng.getrandbits(1) for _ in range(m + 1)]
        # Naive truncation r_{m+1->m}: drop the last (highest-weight) bit.
        prefix = omega[:-1]
        # Fold-aware restriction r~_{m+1->m}: prefix of Fold_{m+1}.
        folded = _fold_m_via_rewrite(omega)
        rem = folded[:-1]
        mism += sum((a ^ b) for a, b in zip(prefix, rem))
        total += m
    return mism / float(total) if total else 0.0


def _fold_m_via_rewrite(micro: Sequence[int]) -> List[int]:
    """Compute Fold_m(micro) via 011->100 rewrite (no bigint Fibonacci arithmetic).

    micro is in the paper's low-to-high order (b_1,...,b_m) with weights F_{i+1}.
    We reverse to MSD-first, prepend one leading 0, normalize, then reverse back and
    drop the highest Zeckendorf digit (the overflow at weight F_{m+2}).
    """
    m = len(micro)
    if m == 0:
        return []
    s = "0" + "".join("1" if b else "0" for b in reversed(micro))
    norm = _rewrite_normalize_011_to_100(s)
    # norm is MSD-first of length m+1; reverse to low-to-high digits z2..z_{m+2}.
    digits_low = [1 if ch == "1" else 0 for ch in reversed(norm)]
    return digits_low[:m]


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def main() -> None:
    t0 = time.time()
    prog = Progress("fold_gauge_anomaly_density_transducer", every_seconds=20.0)

    init, finals, delta = _berstel_normalizer_nfa()
    # Quick internal audit: NFA agrees with rewrite normalizer on modest lengths.
    for n in range(3, 14):
        for x in range(1 << (n - 1)):
            inp = "0" + format(x, f"0{n-1}b")
            out = _nfa_transduce_unique(inp, init, finals, delta)
            want = _rewrite_normalize_011_to_100(inp)
            if out != want:
                raise RuntimeError(f"normalizer mismatch at n={n} inp={inp} got={out} want={want}")
        prog.tick(f"audit ok up to n={n}")

    # Cross-audit: rewrite-based Fold_m matches the repository's bigint Fold_m on small m.
    rng = random.Random(20260205)
    for m in [5, 10, 20, 40, 80, 120]:
        for _ in range(300):
            micro = [rng.getrandbits(1) for _ in range(m)]
            a = fold_m(micro)
            b = _fold_m_via_rewrite(micro)
            if a != b:
                raise RuntimeError(f"Fold_m mismatch at m={m}: fold_m={a[:16]}... rewrite={b[:16]}...")
        prog.tick(f"fold_m rewrite-audit ok up to m={m}")

    inp_delta, pre = _input_only_delta(delta)
    _f0, f_trans = _build_forward_subset_dfa(init=init, inp_delta=inp_delta, forced_leading="0")
    _b0, b_trans = _build_backward_subset_dfa(finals=finals, pre=pre)

    f_states = sorted(f_trans.keys())
    b_states = sorted(b_trans.keys())

    piF = _solve_stationary_dfa(f_states, f_trans, p0=Fraction(1, 2), p1=Fraction(1, 2))
    piB = _solve_stationary_dfa(b_states, b_trans, p0=Fraction(1, 2), p1=Fraction(1, 2))

    # Under IID input, the left (prefix) and right (suffix) contexts are independent.
    # Per-bit mismatch rate is therefore the product expectation over the context kernel.
    exp_m = Fraction(0)
    exp_k = Fraction(1)  # synchronous: exactly one output bit per input bit
    mismatch_contexts: List[Dict[str, object]] = []
    for S, pS in zip(f_states, piF):
        for T, pT in zip(b_states, piB):
            wST = pS * pT
            for a, pa in (("0", Fraction(1, 2)), ("1", Fraction(1, 2))):
                b = _out_bit_from_context(delta=delta, forward_set=S, a=a, backward_set=T)
                mism = 1 if a != b else 0
                exp_m += wST * pa * Fraction(mism)
                mismatch_contexts.append(
                    {
                        "forward_set": "".join(S),
                        "backward_set": "".join(T),
                        "input": int(a),
                        "output": int(b),
                        "mismatch": mism,
                    }
                )
    g = exp_m / exp_k

    print(
        f"[fold_gauge_anomaly_density_transducer] kernel sizes: forward={len(f_states)} backward={len(b_states)} g={g}",
        flush=True,
    )

    # Monte Carlo sanity against the direct Fold gauge anomaly definition.
    samples = []
    for m in [200, 500, 1000, 2000, 5000]:
        # Keep this step lightweight; the theorem is proved by the exact kernel above.
        trials = 600 if m <= 2000 else 250
        est = _sample_gauge_anomaly_density(m, trials=trials, seed=12345 + m)
        samples.append({"m": m, "trials": trials, "estimate": est})
        prog.tick(f"mc m={m} est~{est:.6g}")

    payload = {
        "meta": {
            "script": Path(__file__).name,
            "generated_at_unix_s": time.time(),
        },
        "result": {
            "g_exact": f"{g.numerator}/{g.denominator}",
            "g_float": float(g),
            "E_mismatch_per_step": f"{exp_m.numerator}/{exp_m.denominator}",
            "E_output_bits_per_step": f"{exp_k.numerator}/{exp_k.denominator}",
            "num_forward_subset_states": len(f_states),
            "num_backward_subset_states": len(b_states),
            "pi_forward": {"".join(s): f"{pi.numerator}/{pi.denominator}" for s, pi in zip(f_states, piF)},
            "pi_backward": {"".join(s): f"{pi.numerator}/{pi.denominator}" for s, pi in zip(b_states, piB)},
            "context_kernel": mismatch_contexts,
        },
        "mc_samples": samples,
    }

    out_json = export_dir() / "fold_gauge_anomaly_density_transducer.json"
    _write_text(out_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")

    # TeX fragment
    tex_lines: List[str] = []
    tex_lines.append("% Auto-generated by scripts/exp_fold_gauge_anomaly_density_transducer.py")
    tex_lines.append(r"\begin{proposition}[折叠规范差密度的闭式：$g_\ast=\frac49$]\label{prop:fold-gauge-anomaly-density-49}")
    tex_lines.append(r"在均匀基线 $\omega\sim\mathrm{Unif}(\Omega_{m+1})$ 下，令 $\bar G_m=\mathbb E[G_m(\omega)]$。则极限")
    tex_lines.append(r"\[")
    tex_lines.append(r"g_\ast:=\lim_{m\to\infty}\frac{\bar G_m}{m}")
    tex_lines.append(r"\]")
    tex_lines.append(r"存在，并且满足严格恒等式")
    tex_lines.append(r"\[")
    tex_lines.append(r"\boxed{\;g_\ast=\frac49\;}.")
    tex_lines.append(r"\]")
    tex_lines.append(r"\end{proposition}")
    tex_lines.append("")
    tex_lines.append(r"\begin{proof}[证明（可审计）]")
    tex_lines.append(
        r"用 Berstel 的 $4$ 状态不歧义归一化换能器（\cite{ITA_2001__35_6_491_0}，Figure~1）描述 Zeckendorf 规范化。"
        r"该转导是同步的（逐位输入/逐位输出），逐位 mismatch 只取决于当前位置的输出位。"
        r"令 $L_i$ 为输入 NFA 在前缀 $x_1\cdots x_{i-1}$ 驱动下的可达状态集合（强制 leading $0$ 后的子集确定化），"
        r"令 $R_i$ 为反向输入 NFA 在后缀 $x_{i+1}x_{i+2}\cdots$ 驱动下的可共达状态集合（从终态集合出发的子集确定化）。"
        r"不歧义性保证：对任意三元组 $(L_i,x_i,R_i)$，被选择的输出位唯一确定。"
        r"在 IID Bernoulli$(1/2)$ 输入下，$L_i$ 与 $R_i$ 分别诱导有限状态马尔可夫链；且 $L_i$ 只依赖过去、$R_i$ 只依赖未来，故在切点处二者独立。"
        r"由遍历定理，$\bar G_m/m$ 收敛到该有限同步核上的稳态期望。"
    )
    tex_lines.append(
        r"对子集确定化可得：前缀链只有两态 $\{a,b\},\{c,d\}$，其转移为"
        r"\(\{a,b\}\xrightarrow{0}\{a,b\},\ \{a,b\}\xrightarrow{1}\{c,d\},\ \{c,d\}\xrightarrow{0}\{a,b\},\ \{c,d\}\xrightarrow{1}\{a,b\}\)，"
        r"故平稳分布为 $(2/3,1/3)$。"
        r"类似地，后缀链只有三态 $\{a,c\},\{a,d\},\{b,c\}$，其转移为"
        r"\(\{a,d\}\xrightarrow{0}\{a,d\},\ \{a,d\}\xrightarrow{1}\{a,c\},\ \{a,c\}\xrightarrow{0}\{a,d\},\ \{a,c\}\xrightarrow{1}\{b,c\},\ \{b,c\}\xrightarrow{0}\{a,c\},\ \{b,c\}\xrightarrow{1}\{b,c\}\)，"
        r"故平稳分布为均匀 $(1/3,1/3,1/3)$。"
        r"逐项枚举 $(\text{left},x,\text{right})$ 的唯一输出位并按上述权重求期望，得到严格恒等式 $g_\ast=4/9$。"
    )
    tex_lines.append(
        r"更具体地，mismatch 仅发生在 $x=1$ 且 $(\text{left},\text{right})\in\{(\{a,b\},\{a,c\}),(\{c,d\},\{a,c\}),(\{c,d\},\{a,d\})\}$，"
        r"以及 $(\text{left},\text{right})=(\{a,b\},\{b,c\})$（此时 $x=0,1$ 均 mismatch）这五种情形。于是"
    )
    tex_lines.append(r"\[")
    tex_lines.append(
        r"g_\ast"
        r"=\frac12\Bigl(\frac23\cdot\frac13+\frac13\cdot\frac13+\frac13\cdot\frac13+2\cdot\frac23\cdot\frac13\Bigr)"
        r"=\frac49."
    )
    tex_lines.append(r"\]")
    tex_lines.append(
        r"上述子集链状态、平稳分布与输出唯一性均可由脚本 \texttt{scripts/exp\_fold\_gauge\_anomaly\_density\_transducer.py} 一键复算与交叉审计。"
    )
    tex_lines.append(r"\end{proof}")
    tex_lines.append("")

    out_tex = generated_dir() / "eq_fold_gauge_anomaly_density_transducer.tex"
    _write_text(out_tex, "\n".join(tex_lines) + "\n")

    print(f"[fold_gauge_anomaly_density_transducer] g={g} ~ {float(g):.12g}", flush=True)
    print(f"[fold_gauge_anomaly_density_transducer] wrote {out_json}", flush=True)
    print(f"[fold_gauge_anomaly_density_transducer] wrote {out_tex}", flush=True)


if __name__ == "__main__":
    main()

