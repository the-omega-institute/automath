#!/usr/bin/env python3
"""Numerically verify cylinder-information rigidity on sample mixing SFTs."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from typing import Dict, List, Tuple

import numpy as np


ZERO_TOLERANCE = 1.0e-12
POSITIVE_TOLERANCE = 1.0e-10
MINIMUM_PARRY_DISTANCE = 2.0e-2


def example_adjacencies() -> Dict[str, np.ndarray]:
    """Return primitive zero-one matrices on alphabets of sizes 2 through 5."""
    return {
        "golden_mean_k2": np.array(
            [[1, 1], [1, 0]], dtype=float
        ),
        "looped_cycle_k3": np.array(
            [[1, 1, 0], [0, 1, 1], [1, 0, 1]], dtype=float
        ),
        "chorded_cycle_k4": np.array(
            [[1, 1, 0, 0], [0, 1, 1, 0], [1, 0, 1, 1], [1, 0, 0, 1]],
            dtype=float,
        ),
        "asymmetric_k5": np.array(
            [
                [1, 1, 0, 0, 0],
                [0, 1, 1, 0, 1],
                [1, 0, 1, 1, 0],
                [0, 1, 0, 1, 1],
                [1, 0, 0, 0, 1],
            ],
            dtype=float,
        ),
    }


def is_primitive(adjacency: np.ndarray) -> bool:
    """Check primitivity by the finite Wielandt bound."""
    adjacency = np.asarray(adjacency, dtype=int)
    k = adjacency.shape[0]
    power = np.eye(k, dtype=np.int64)
    for _ in range(1, (k - 1) ** 2 + 2):
        power = power @ adjacency
        if np.all(power > 0):
            return True
    return False


def parry_transition(adjacency: np.ndarray) -> Tuple[np.ndarray, float]:
    """Construct the Parry transition matrix and Perron eigenvalue."""
    adjacency = np.asarray(adjacency, dtype=float)
    eigenvalues, eigenvectors = np.linalg.eig(adjacency)
    index = int(np.argmax(eigenvalues.real))
    eigenvalue = float(eigenvalues[index].real)
    right = np.asarray(eigenvectors[:, index].real, dtype=float)
    if np.sum(right) < 0:
        right = -right
    if eigenvalue <= 0 or np.any(right <= 0):
        raise ValueError("adjacency matrix has no positive Perron eigenvector")
    transition = adjacency * right[np.newaxis, :] / (
        eigenvalue * right[:, np.newaxis]
    )
    transition /= transition.sum(axis=1, keepdims=True)
    return transition, eigenvalue


def stationary_distribution(transition: np.ndarray) -> np.ndarray:
    """Solve pi P = pi together with sum(pi) = 1."""
    transition = np.asarray(transition, dtype=float)
    k = transition.shape[0]
    system = transition.T - np.eye(k)
    system[-1, :] = 1.0
    target = np.zeros(k)
    target[-1] = 1.0
    stationary = np.linalg.solve(system, target)
    return stationary


def asymptotic_information_variance(
    transition: np.ndarray, adjacency: np.ndarray
) -> float:
    """Compute the martingale/Poisson asymptotic variance of -log P_ij."""
    transition = np.asarray(transition, dtype=float)
    allowed = np.asarray(adjacency, dtype=bool)
    if transition.shape != allowed.shape:
        raise ValueError("transition and adjacency shapes differ")
    if np.any(transition[allowed] <= 0) or np.any(transition[~allowed] != 0):
        raise ValueError("transition is not fully supported on the allowed edges")
    if not np.allclose(transition.sum(axis=1), 1.0, atol=1.0e-12):
        raise ValueError("transition rows do not sum to one")

    stationary = stationary_distribution(transition)
    edge_information = np.zeros_like(transition)
    edge_information[allowed] = -np.log(transition[allowed])
    row_mean = np.sum(transition * edge_information, axis=1)
    entropy = float(stationary @ row_mean)

    # (I-P)v = row_mean-h, with pi(v)=0 fixing the additive constant.
    poisson_matrix = (
        np.eye(transition.shape[0])
        - transition
        + np.ones((transition.shape[0], 1)) @ stationary[np.newaxis, :]
    )
    transfer = np.linalg.solve(poisson_matrix, row_mean - entropy)
    martingale_increment = (
        edge_information
        - entropy
        + transfer[np.newaxis, :]
        - transfer[:, np.newaxis]
    )
    variance = float(
        np.sum(stationary[:, np.newaxis] * transition * martingale_increment**2)
    )
    return variance


def random_non_parry_transition(
    adjacency: np.ndarray, parry: np.ndarray, rng: np.random.Generator
) -> np.ndarray:
    """Sample a fully supported chain separated from the Parry matrix."""
    adjacency = np.asarray(adjacency, dtype=bool)
    for _ in range(10_000):
        proposal = np.zeros_like(parry)
        for i in range(adjacency.shape[0]):
            weights = rng.gamma(shape=1.5, scale=1.0, size=int(adjacency[i].sum()))
            proposal[i, adjacency[i]] = weights / weights.sum()
        strength = rng.uniform(0.25, 0.95)
        transition = (1.0 - strength) * parry + strength * proposal
        if np.linalg.norm(transition - parry) >= MINIMUM_PARRY_DISTANCE:
            return transition
    raise RuntimeError("could not sample a transition separated from the Parry matrix")


@dataclass(frozen=True)
class ShiftResult:
    name: str
    states: int
    perron_eigenvalue: float
    primitive: bool
    parry_variance: float
    non_parry_samples: int
    minimum_non_parry_variance: float
    maximum_non_parry_variance: float
    counterexamples: int


@dataclass(frozen=True)
class VerificationReport:
    seed: int
    samples_per_shift: int
    results: Tuple[ShiftResult, ...]
    mme_zero_confirmations: int
    non_mme_positive_confirmations: int
    failures: int
    counterexamples: int


def run_counterexample_search(
    samples_per_shift: int = 500, seed: int = 20260801
) -> VerificationReport:
    """Test the MME and search seeded non-MME samples for zero variance."""
    rng = np.random.default_rng(seed)
    results: List[ShiftResult] = []
    mme_zero_confirmations = 0
    non_mme_positive_confirmations = 0
    failures = 0
    counterexamples = 0

    for name, adjacency in example_adjacencies().items():
        try:
            primitive = is_primitive(adjacency)
            if not primitive:
                raise ValueError(f"{name} is not primitive")
            parry, eigenvalue = parry_transition(adjacency)
            parry_variance = asymptotic_information_variance(parry, adjacency)
            if abs(parry_variance) <= ZERO_TOLERANCE:
                mme_zero_confirmations += 1
            else:
                counterexamples += 1

            non_parry_variances = []
            shift_counterexamples = 0
            for _ in range(samples_per_shift):
                transition = random_non_parry_transition(adjacency, parry, rng)
                variance = asymptotic_information_variance(transition, adjacency)
                non_parry_variances.append(variance)
                if variance > POSITIVE_TOLERANCE:
                    non_mme_positive_confirmations += 1
                else:
                    shift_counterexamples += 1
                    counterexamples += 1

            results.append(
                ShiftResult(
                    name=name,
                    states=adjacency.shape[0],
                    perron_eigenvalue=eigenvalue,
                    primitive=primitive,
                    parry_variance=parry_variance,
                    non_parry_samples=samples_per_shift,
                    minimum_non_parry_variance=min(non_parry_variances),
                    maximum_non_parry_variance=max(non_parry_variances),
                    counterexamples=shift_counterexamples,
                )
            )
        except (ValueError, RuntimeError, np.linalg.LinAlgError):
            failures += 1

    return VerificationReport(
        seed=seed,
        samples_per_shift=samples_per_shift,
        results=tuple(results),
        mme_zero_confirmations=mme_zero_confirmations,
        non_mme_positive_confirmations=non_mme_positive_confirmations,
        failures=failures,
        counterexamples=counterexamples,
    )


def format_report(report: VerificationReport) -> str:
    lines = [
        "GENERAL MIXING-SFT CYLINDER-INFORMATION RIGIDITY VERIFICATION",
        f"seed: {report.seed}",
        f"samples per shift: {report.samples_per_shift}",
        f"MME zero tolerance: {ZERO_TOLERANCE:.1e}",
        f"non-MME positive tolerance: {POSITIVE_TOLERANCE:.1e}",
        f"minimum Frobenius distance from Parry matrix: {MINIMUM_PARRY_DISTANCE:.2e}",
        "",
    ]
    for result in report.results:
        lines.extend(
            [
                f"[{result.name}]",
                f"states k: {result.states}",
                f"primitive (irreducible and aperiodic): {result.primitive}",
                f"Perron eigenvalue: {result.perron_eigenvalue:.15g}",
                f"Parry/MME asymptotic variance: {result.parry_variance:.16e}",
                f"non-MME samples: {result.non_parry_samples}",
                "non-MME variance range: "
                f"[{result.minimum_non_parry_variance:.16e}, "
                f"{result.maximum_non_parry_variance:.16e}]",
                f"counterexamples in this shift: {result.counterexamples}",
                "",
            ]
        )
    lines.extend(
        [
            "SUMMARY",
            f"MME zero-variance confirmations: {report.mme_zero_confirmations}",
            "non-MME positive-variance confirmations: "
            f"{report.non_mme_positive_confirmations}",
            f"failures: {report.failures}",
            f"counterexamples: {report.counterexamples}",
            f"{report.failures} failures / {report.counterexamples} counterexamples",
            "RESULT: PASS"
            if report.failures == 0 and report.counterexamples == 0
            else "RESULT: FAIL",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples-per-shift", type=int, default=500)
    parser.add_argument("--seed", type=int, default=20260801)
    args = parser.parse_args()
    report = run_counterexample_search(args.samples_per_shift, args.seed)
    print(format_report(report))
    return 0 if report.failures == 0 and report.counterexamples == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
