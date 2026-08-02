#!/usr/bin/env python3
"""Deterministic numerical checks for the banked SRG rigidity note.

The computations are evidence and regression tests, not proofs.  They check
finite-memory instances of the martingale variance formula, an FGM renewal
truncation, the oscillatory distortion mechanism, and finite-depth versions
of the full-support atomic counterexample.
"""

from __future__ import annotations

import math
from collections import defaultdict

import numpy as np


SEED = 20260802
ZERO_TOL = 1.0e-11
POS_TOL = 1.0e-9


def stationary_distribution(p: np.ndarray) -> np.ndarray:
    n = p.shape[0]
    a = p.T - np.eye(n)
    a[-1, :] = 1.0
    b = np.zeros(n)
    b[-1] = 1.0
    return np.linalg.solve(a, b)


def edge_information_variance(p: np.ndarray) -> float:
    """Poisson/martingale asymptotic variance of -log P_ij."""
    pi = stationary_distribution(p)
    allowed = p > 0.0
    info = np.zeros_like(p)
    info[allowed] = -np.log(p[allowed])
    row_mean = np.sum(p * info, axis=1)
    entropy = float(pi @ row_mean)
    poisson = np.eye(len(p)) - p + np.ones((len(p), 1)) @ pi[None, :]
    u = np.linalg.solve(poisson, row_mean - entropy)
    martingale = info - entropy + u[None, :] - u[:, None]
    return float(np.sum(pi[:, None] * p * martingale**2))


def parry_transition(a: np.ndarray) -> np.ndarray:
    vals, vecs = np.linalg.eig(a.astype(float))
    idx = int(np.argmax(vals.real))
    lam = float(vals[idx].real)
    r = vecs[:, idx].real
    if r.sum() < 0:
        r = -r
    p = a * r[None, :] / (lam * r[:, None])
    p /= p.sum(axis=1, keepdims=True)
    return p


def random_markov_search(rng: np.random.Generator) -> tuple[int, float, float]:
    adjacencies = [
        np.array([[1, 1], [1, 0]], dtype=float),
        np.array([[1, 1, 0], [0, 1, 1], [1, 0, 1]], dtype=float),
    ]
    parry_max = 0.0
    nonparry_min = math.inf
    samples = 0
    for a in adjacencies:
        parry = parry_transition(a)
        parry_max = max(parry_max, abs(edge_information_variance(parry)))
        allowed = a.astype(bool)
        for _ in range(600):
            q = np.zeros_like(a)
            for i in range(len(a)):
                weights = rng.gamma(1.4, 1.0, int(allowed[i].sum()))
                q[i, allowed[i]] = weights / weights.sum()
            if np.linalg.norm(q - parry) < 0.03:
                continue
            variance = edge_information_variance(q)
            nonparry_min = min(nonparry_min, variance)
            samples += 1
    return samples, parry_max, nonparry_min


def order_two_search(rng: np.random.Generator) -> tuple[int, float, float]:
    """Search binary two-step Markov measures, beyond one-step output laws."""
    states = [(0, 0), (0, 1), (1, 0), (1, 1)]
    index = {state: i for i, state in enumerate(states)}

    def matrix(q: np.ndarray) -> np.ndarray:
        p = np.zeros((4, 4))
        for i, (a, b) in enumerate(states):
            p[i, index[(b, 1)]] = q[i]
            p[i, index[(b, 0)]] = 1.0 - q[i]
        return p

    fair_variance = edge_information_variance(matrix(np.full(4, 0.5)))
    minimum = math.inf
    samples = 0
    for _ in range(1200):
        q = rng.uniform(0.08, 0.92, 4)
        if np.linalg.norm(q - 0.5) < 0.08:
            continue
        variance = edge_information_variance(matrix(q))
        minimum = min(minimum, variance)
        samples += 1
    return samples, fair_variance, minimum


def fgm_v(k: int) -> float:
    r = math.ceil((math.sqrt(8 * (k + 1) + 1) - 1) / 2)
    return (-1.0 if r % 2 else 1.0) / r


def fgm_checks() -> dict[str, float]:
    n = 20000
    v = np.fromiter((fgm_v(k) for k in range(n)), dtype=float, count=n)
    partial = np.concatenate(([0.0], np.cumsum(v)))
    interval_sum_bound = float(partial.max() - partial.min())

    p_inf = 0.5
    xi = 1.5
    p = 1.0 - (1.0 - p_inf) * np.power(xi, v)
    variation_envelope = np.maximum.accumulate(np.abs(p[::-1] - p_inf))[::-1]
    variation_sum = float(variation_envelope[:n].sum())

    # Finite-age Markov approximation to the renewal chain.  State a is the
    # current zero-run age.  At the cutoff, a failed renewal remains at K.
    cutoff = 120
    p_cut = p[: cutoff + 1]
    transition = np.zeros((cutoff + 1, cutoff + 1))
    for age in range(cutoff):
        transition[age, 0] = p_cut[age]
        transition[age, age + 1] = 1.0 - p_cut[age]
    transition[cutoff, 0] = p_cut[cutoff]
    transition[cutoff, cutoff] = 1.0 - p_cut[cutoff]
    renewal_variance = edge_information_variance(transition)

    limit_one = (1.0 - p_inf) * xi / ((1.0 - p_inf) * xi + p_inf)
    limit_two = 1.0 - p_inf
    return {
        "partial_min": float(partial.min()),
        "partial_max": float(partial.max()),
        "interval_sum_bound": interval_sum_bound,
        "variation_sum": variation_sum,
        "variation_over_sqrt_n": variation_sum / math.sqrt(n),
        "renewal_variance": renewal_variance,
        "conditional_limit_gap": abs(limit_one - limit_two),
    }


def primitive_period(word: tuple[int, ...]) -> tuple[int, ...]:
    for p in range(1, len(word) + 1):
        if len(word) % p == 0 and word == word[:p] * (len(word) // p):
            return word[:p]
    return word


def periodic_prefix(period: tuple[int, ...], n: int) -> tuple[int, ...]:
    return tuple(period[i % len(period)] for i in range(n))


def atomic_counterexample(depth: int = 10) -> dict[str, float]:
    """Finite-depth truncation of sum 2^{-2L} over all periodic words."""
    atoms: dict[tuple[int, ...], float] = defaultdict(float)
    for length in range(1, depth + 1):
        layer_atom_weight = 2.0 ** (-2 * length)
        for value in range(2**length):
            word = tuple((value >> (length - 1 - j)) & 1 for j in range(length))
            atoms[primitive_period(word)] += layer_atom_weight
    total = sum(atoms.values())
    weights = {atom: weight / total for atom, weight in atoms.items()}

    all_depth_words = {
        periodic_prefix(atom, depth) for atom in weights
    }
    coverage = len(all_depth_words)

    variances = []
    for n in range(1, 2 * depth + 3):
        cylinder_mass: dict[tuple[int, ...], float] = defaultdict(float)
        for atom, weight in weights.items():
            cylinder_mass[periodic_prefix(atom, n)] += weight
        infos = []
        probs = []
        for atom, weight in weights.items():
            infos.append(-math.log(cylinder_mass[periodic_prefix(atom, n)]))
            probs.append(weight)
        info = np.array(infos)
        prob = np.array(probs)
        mean = float(prob @ info)
        variances.append(float(prob @ ((info - mean) ** 2)))

    return {
        "atoms": float(len(weights)),
        "covered_depth_words": float(coverage),
        "required_depth_words": float(2**depth),
        "max_variance": max(variances),
        "terminal_variance": variances[-1],
        "terminal_variance_rate": variances[-1] / (2 * depth + 2),
    }


def main() -> int:
    rng = np.random.default_rng(SEED)
    markov_samples, parry_max, markov_min = random_markov_search(rng)
    order2_samples, fair_variance, order2_min = order_two_search(rng)
    fgm = fgm_checks()
    atomic = atomic_counterexample()

    checks = {
        "Parry finite-state variance is numerical zero": parry_max < ZERO_TOL,
        "non-Parry finite-state search is positive": markov_min > POS_TOL,
        "fair order-two chain is numerical zero": abs(fair_variance) < ZERO_TOL,
        "nonfair order-two search is positive": order2_min > POS_TOL,
        "FGM interval sums are bounded": fgm["interval_sum_bound"] <= 1.0000001,
        "FGM truncation has positive information variance": fgm["renewal_variance"] > POS_TOL,
        "FGM two-sided conditional signatures differ": fgm["conditional_limit_gap"] > 0.05,
        "atomic truncation covers every word at tested depth": atomic["covered_depth_words"] == atomic["required_depth_words"],
        "atomic information variance is bounded in tested range": atomic["max_variance"] < 20.0,
    }

    print("TILT INTERIOR / NON-GIBBS RIGIDITY VERIFICATION")
    print(f"seed: {SEED}")
    print()
    print("FINITE-MEMORY CHARACTERIZATION SEARCH")
    print(f"random one-step samples: {markov_samples}")
    print(f"largest |Parry variance|: {parry_max:.16e}")
    print(f"smallest separated non-Parry variance: {markov_min:.16e}")
    print(f"random binary order-two samples: {order2_samples}")
    print(f"fair Bernoulli variance in order-two presentation: {fair_variance:.16e}")
    print(f"smallest separated nonfair order-two variance: {order2_min:.16e}")
    print()
    print("FERNANDEZ-GALLO-MAILLARD OSCILLATORY RENEWAL CHECK")
    print(f"partial-sum range through 20000: [{fgm['partial_min']:.12f}, {fgm['partial_max']:.12f}]")
    print(f"maximum interval-sum magnitude proxy: {fgm['interval_sum_bound']:.12f}")
    print(f"sum of one-step continuity envelope: {fgm['variation_sum']:.12f}")
    print(f"continuity-envelope sum / sqrt(20000): {fgm['variation_over_sqrt_n']:.12f}")
    print(f"age-120 renewal information variance: {fgm['renewal_variance']:.16e}")
    print(f"published two-sided conditional limit gap: {fgm['conditional_limit_gap']:.12f}")
    print()
    print("FULL-SUPPORT ATOMIC COUNTEREXAMPLE (FINITE-DEPTH TRUNCATION)")
    print(f"distinct periodic atoms: {int(atomic['atoms'])}")
    print(f"depth-10 cylinders covered: {int(atomic['covered_depth_words'])}/{int(atomic['required_depth_words'])}")
    print(f"maximum information variance over n=1..22: {atomic['max_variance']:.12f}")
    print(f"terminal information variance: {atomic['terminal_variance']:.12f}")
    print(f"terminal variance/n: {atomic['terminal_variance_rate']:.12f}")
    print()
    print("CHECKS")
    for name, passed in checks.items():
        print(f"[{'PASS' if passed else 'FAIL'}] {name}")
    failures = sum(not passed for passed in checks.values())
    print()
    print(f"SUMMARY: {len(checks) - failures}/{len(checks)} checks passed")
    print("RESULT: PASS" if failures == 0 else "RESULT: FAIL")
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
