#!/usr/bin/env python3
"""Finite-layer consistency check for critical Fibonacci Gibbs geometry.

This is a diagnostic for signs and constants, not evidence for distributional
convergence.  It samples the exact pushforward of the finite-layer Gibbs law
to Weinstein's generator cost and word length via the renewal identity in the
paper.  Only Python's standard library and NumPy are required.
"""

from __future__ import annotations

import os

import argparse
import math
import sys
import time
from dataclasses import dataclass
from pathlib import Path

import numpy as np


SEED = 20_260_817
SIGMA_0 = 2.4787507857339603
ALPHA = SIGMA_0 - 1.0
B_C = 8.0
K_C = 2.0 ** (SIGMA_0 - 1.0) * B_C / ALPHA
DEFAULT_LADDER = (200, 800, 2_400)
MU_CAPS = (300, 1_000, 3_000, 10_000, 30_000)
MU_SELECTED_CAP = 3_000
BIN_CENTERS = (0.25, 0.50, 0.75)
BIN_HALF_WIDTH = 0.06
QUANTILE_LEVELS = (0.10, 0.50, 0.90)


def negative_cf_cost(p: int, q: int, cap: int | None = None) -> int:
    """Return c(p/q)=2 sum(e_i-1)+1 for a reduced 0<p<q.

    The regular Euclidean quotients have sum one larger than
    sum(e_i-1), so the equivalent exact calculation is
    c(p/q)=2*sum(a_i)-1.  ``cap`` returns min(c(p/q), cap), which is
    sufficient for rejection at a finite layer and for capped means.
    """
    if not (0 < p < q) or math.gcd(p, q) != 1:
        raise ValueError("p/q must be a reduced fraction strictly between 0 and 1")
    digit_sum = 0
    while p:
        quotient, remainder = divmod(q, p)
        digit_sum += quotient
        value = 2 * digit_sum - 1
        if cap is not None and value >= cap:
            return cap
        q, p = p, remainder
    return 2 * digit_sum - 1


def _uniform_numerator_large_q(rng: np.random.Generator, q: int) -> int:
    """Draw uniformly from 1,...,q when q exceeds exact float resolution."""
    modulus = 1 << 64
    limit = modulus - modulus % q
    while True:
        raw = int(rng.bit_generator.random_raw())
        if raw < limit:
            return raw % q + 1


class LetterSampler:
    """Sample the critical letter cost C, optionally capped.

    If Q has the Zipf(alpha) law and P is uniform on 1,...,Q, rejection
    on Q>=2 and gcd(P,Q)=1 assigns every accepted reduced P/Q mass
    proportional to Q^(-alpha-1)=Q^(-sigma_0).  At the critical root the
    accepted masses sum to one, exactly the letter law in the paper.
    """

    def __init__(
        self,
        rng: np.random.Generator,
        alpha: float,
        cap: int,
        batch_size: int = 250_000,
    ) -> None:
        self.rng = rng
        self.alpha = alpha
        self.cap = cap
        self.batch_size = batch_size
        self._buffer = np.empty(0, dtype=np.int32)
        self._position = 0
        self.draw_count = 0

    def _refill(self) -> None:
        accepted_pairs: list[np.ndarray] = []
        accepted_count = 0
        proposal_size = max(20_000, self.batch_size * 3)
        while accepted_count < self.batch_size:
            q = self.rng.zipf(self.alpha, proposal_size)
            p = np.floor(self.rng.random(proposal_size) * q).astype(np.int64) + 1
            large = np.flatnonzero(q > (1 << 53))
            for index in large:
                p[index] = _uniform_numerator_large_q(self.rng, int(q[index]))
            keep = (q >= 2) & (np.gcd(p, q) == 1)
            pairs = np.column_stack((p[keep], q[keep]))
            accepted_pairs.append(pairs)
            accepted_count += len(pairs)

        pairs = np.concatenate(accepted_pairs, axis=0)[: self.batch_size]
        costs = np.empty(self.batch_size, dtype=np.int32)
        for index, (p, q) in enumerate(pairs):
            costs[index] = negative_cf_cost(int(p), int(q), self.cap)
        self._buffer = costs
        self._position = 0

    def take(self, count: int) -> np.ndarray:
        """Return ``count`` independent capped critical-letter costs."""
        pieces: list[np.ndarray] = []
        remaining = count
        while remaining:
            if self._position == len(self._buffer):
                self._refill()
            available = min(remaining, len(self._buffer) - self._position)
            pieces.append(self._buffer[self._position : self._position + available])
            self._position += available
            remaining -= available
        self.draw_count += count
        return np.concatenate(pieces) if len(pieces) > 1 else pieces[0].copy()


@dataclass(frozen=True)
class LayerSamples:
    cost: np.ndarray
    length: np.ndarray
    proposal_count: int


def sample_layer(
    rng: np.random.Generator,
    letters: LetterSampler,
    m: int,
    sample_count: int,
) -> LayerSamples:
    """Sample (J_m,H_m) from the exact finite-layer Gibbs pushforward.

    A proposal length is uniform on 0,...,floor(m/3).  The endpoint proposal
    is accepted with probability 1/2; nonempty words of cost below m are
    accepted; words of cost m are accepted with probability 1/2.  Rejection
    therefore leaves the exact orbit multiplicities 1, 2, and 1.  Each
    accepted word represents the corresponding point(s) N in the layer.  The
    integer orbit representative is not materialized because both points in
    a subterminal orbit have the same generator, hence the same (J_m,H_m).
    """
    if letters.cap < m + 1:
        raise ValueError("letter cap must be at least m+1")
    max_length = m // 3
    costs_out: list[np.ndarray] = []
    lengths_out: list[np.ndarray] = []
    obtained = 0
    proposals = 0

    while obtained < sample_count:
        remaining = sample_count - obtained
        batch = max(4_000, 9 * remaining)
        proposed_length = rng.integers(0, max_length + 1, size=batch, dtype=np.int32)
        cost = np.zeros(batch, dtype=np.int32)
        length = np.zeros(batch, dtype=np.int32)

        while True:
            active = (length < proposed_length) & (cost <= m)
            if not np.any(active):
                break
            indices = np.flatnonzero(active)
            increments = letters.take(len(indices))
            cost[indices] += increments
            length[indices] += 1

        coin = rng.random(batch)
        endpoint = (proposed_length == 0) & (coin < 0.5)
        complete = (proposed_length > 0) & (length == proposed_length)
        subterminal = complete & (cost < m)
        terminal = complete & (cost == m) & (coin < 0.5)
        accepted = endpoint | subterminal | terminal
        accepted_cost = cost[accepted]
        accepted_length = length[accepted]
        costs_out.append(accepted_cost)
        lengths_out.append(accepted_length)
        obtained += len(accepted_cost)
        proposals += batch

    return LayerSamples(
        cost=np.concatenate(costs_out)[:sample_count],
        length=np.concatenate(lengths_out)[:sample_count],
        proposal_count=proposals,
    )


def sample_spectrally_positive_stable(
    rng: np.random.Generator, alpha: float, count: int
) -> np.ndarray:
    """Sample the stable law with exponent alpha*Gamma(-alpha)*(-it)^alpha."""
    angle = rng.uniform(-math.pi / 2.0, math.pi / 2.0, count)
    exponential = rng.exponential(1.0, count)
    tangent = math.tan(math.pi * alpha / 2.0)
    shift = math.atan(tangent) / alpha
    multiplier = (1.0 + tangent * tangent) ** (1.0 / (2.0 * alpha))
    standard = (
        multiplier
        * np.sin(alpha * (angle + shift))
        / np.cos(angle) ** (1.0 / alpha)
        * (
            np.cos(angle - alpha * (angle + shift)) / exponential
        ) ** ((1.0 - alpha) / alpha)
    )
    levy_scale = (
        -alpha * math.gamma(-alpha) * math.cos(math.pi * alpha / 2.0)
    ) ** (1.0 / alpha)
    return levy_scale * standard


def prediction_factor(t: float, mu_c: float, alpha: float, mutation: str) -> float:
    """Coefficient multiplying S_alpha in a selected predicted law."""
    if mutation not in {"theorem", "flip-sign", "mu-power"}:
        raise ValueError(f"unknown prediction {mutation!r}")
    mu_power = -1.0 - 1.0 / alpha if mutation != "mu-power" else -1.0 / alpha
    sign = -1.0 if mutation != "flip-sign" else 1.0
    return sign * mu_c**mu_power * t ** (1.0 / alpha)


def empirical_ks_uniform(values: np.ndarray) -> float:
    ordered = np.sort(values)
    count = len(ordered)
    ranks = np.arange(1, count + 1) / count
    return float(max(np.max(ranks - ordered), np.max(ordered - (ranks - 1.0 / count))))


@dataclass(frozen=True)
class ConditionalResult:
    center: float
    count: int
    observed: np.ndarray
    predicted: np.ndarray
    spread_discrepancy: float
    relative_spread_discrepancy: float
    median_discrepancy: float
    normalized_median_discrepancy: float
    observed_skew: float
    predicted_skew: float


def quantile_skew(quantiles: np.ndarray) -> float:
    spread = quantiles[2] - quantiles[0]
    return float((quantiles[2] + quantiles[0] - 2.0 * quantiles[1]) / spread)


def conditional_results(
    samples: LayerSamples,
    m: int,
    mu_c: float,
    stable_sample: np.ndarray,
    mutation: str,
) -> list[ConditionalResult]:
    t_values = samples.cost / m
    a_m = (K_C * m) ** (1.0 / ALPHA)
    fluctuation = (samples.length - samples.cost / mu_c) / a_m
    results: list[ConditionalResult] = []
    for center in BIN_CENTERS:
        selected = np.abs(t_values - center) <= BIN_HALF_WIDTH
        observed = np.quantile(fluctuation[selected], QUANTILE_LEVELS)
        predicted = np.quantile(
            prediction_factor(center, mu_c, ALPHA, mutation) * stable_sample,
            QUANTILE_LEVELS,
        )
        observed_spread = observed[2] - observed[0]
        predicted_spread = predicted[2] - predicted[0]
        spread_discrepancy = observed_spread - predicted_spread
        results.append(
            ConditionalResult(
                center=center,
                count=int(np.count_nonzero(selected)),
                observed=observed,
                predicted=predicted,
                spread_discrepancy=float(spread_discrepancy),
                relative_spread_discrepancy=float(
                    abs(spread_discrepancy) / predicted_spread
                ),
                median_discrepancy=float(observed[1] - predicted[1]),
                normalized_median_discrepancy=float(
                    abs(observed[1] - predicted[1]) / predicted_spread
                ),
                observed_skew=quantile_skew(observed),
                predicted_skew=quantile_skew(predicted),
            )
        )
    return results


def prediction_status(results: list[ConditionalResult]) -> tuple[bool, list[str]]:
    reasons: list[str] = []
    if min(result.count for result in results) < 500:
        reasons.append("a conditional bin has fewer than 500 samples")
    relative_spreads = [result.relative_spread_discrepancy for result in results]
    if max(relative_spreads) > 0.50 or float(np.mean(relative_spreads)) > 0.35:
        reasons.append("conditional spread discrepancy exceeds tolerance")
    if max(result.normalized_median_discrepancy for result in results) > 0.30:
        reasons.append("conditional centring discrepancy exceeds tolerance")
    for result in results:
        if abs(result.observed_skew) < 0.03:
            reasons.append(f"observed skew at t={result.center:.2f} is inconclusive")
        elif math.copysign(1.0, result.observed_skew) != math.copysign(
            1.0, result.predicted_skew
        ):
            reasons.append(f"spectral sign is wrong at t={result.center:.2f}")
    return not reasons, reasons


def format_report(
    seed: int,
    calibration_count: int,
    mu_rows: list[tuple[int, float, float, float, float]],
    mu_c: float,
    layer_rows: list[tuple[int, LayerSamples, float, list[float]]],
    stable_sample: np.ndarray,
    predictions: tuple[str, ...],
    elapsed: float,
) -> tuple[str, bool]:
    lines = [
        "Critical Gibbs geometry finite-layer consistency check",
        "======================================================",
        "",
        "PURPOSE: catches sign and normalization errors; it does not test or prove",
        "a distributional limit.",
        f"seed = {seed}",
        f"sigma_0 = {SIGMA_0:.16f}",
        f"alpha = sigma_0 - 1 = {ALPHA:.16f}",
        f"b_C = {B_C:.1f}",
        f"K_C = {K_C:.15f}",
        "",
        "Definitions implemented",
        "-----------------------",
        "letter: reduced p/q with 0<p<q; Pr{p/q}=q^(-sigma_0)",
        "negative-CF cost: d(p/q)=sum_i(e_i-1), c(p/q)=2d(p/q)+1",
        "word: H_m=number of letters, J_m=sum of letter costs=L(g)",
        "layer multiplicities: endpoint 1, cost j<m has 2 orbit points, cost m has 1",
        "G_m{N}=R(N)^(-sigma_0)/Z_m^R(-sigma_0)",
        "a_m=(K_C*m)^(1/alpha)",
        "",
        f"mu_C calibration ({calibration_count} independent critical letters)",
        "----------------------------------------------------------------",
        "cap T      E[min(C,T)]   tail correction    mu estimate       MC SE",
    ]
    for cap, capped_mean, correction, estimate, standard_error in mu_rows:
        lines.append(
            f"{cap:6d}      {capped_mean:11.6f}   {correction:15.6f}"
            f"   {estimate:11.6f}   {standard_error:9.6f}"
        )
    lines.extend(
        [
            f"selected mu_C estimate (predeclared T={MU_SELECTED_CAP}) = {mu_c:.9f}",
            "tail correction = K_C/(alpha-1)*T^(1-alpha); cap ladder is shown to",
            "make its finite-T sensitivity visible.",
            "",
            "Uniform-marginal check",
            "----------------------",
            "m       samples  proposals  accept rate   KS distance   F(.25)-.25  F(.50)-.50  F(.75)-.75",
        ]
    )
    ks_values: list[float] = []
    for m, samples, ks, cdf_discrepancies in layer_rows:
        ks_values.append(ks)
        lines.append(
            f"{m:5d}   {len(samples.cost):7d}  {samples.proposal_count:9d}"
            f"    {len(samples.cost)/samples.proposal_count:8.5f}"
            f"     {ks:9.6f}"
            + "".join(f"    {value:+10.6f}" for value in cdf_discrepancies)
        )
    uniform_ok = ks_values[-1] <= 0.05 and ks_values[-1] < ks_values[0]
    lines.append(
        "uniform gate: "
        + ("PASS" if uniform_ok else "RED")
        + " (final KS <= 0.05 and smaller than first-ladder KS)"
    )

    baseline_ok = False
    final_m, final_samples, _, _ = layer_rows[-1]
    for prediction in predictions:
        lines.extend(
            [
                "",
                f"Conditional check: {prediction}",
                "-" * (19 + len(prediction)),
                "Each row shows observed vs predicted q10/q50/q90 of",
                "Y_m=(H_m-J_m/mu_C)/a_m in |J_m/m-t|<=0.06.",
                "t      count    observed q10/q50/q90          predicted q10/q50/q90"
                "         spread obs-pred (relative)   median obs-pred/norm   skew obs/pred",
            ]
        )
        final_results: list[ConditionalResult] = []
        for m, samples, _, _ in layer_rows:
            results = conditional_results(samples, m, mu_c, stable_sample, prediction)
            lines.append(f"m={m}")
            for result in results:
                lines.append(
                    f"{result.center:4.2f}  {result.count:7d}   "
                    f"[{result.observed[0]:+8.4f},{result.observed[1]:+8.4f},{result.observed[2]:+8.4f}]   "
                    f"[{result.predicted[0]:+8.4f},{result.predicted[1]:+8.4f},{result.predicted[2]:+8.4f}]   "
                    f"{result.spread_discrepancy:+8.4f} ({result.relative_spread_discrepancy:6.3f})   "
                    f"{result.median_discrepancy:+8.4f}/{result.normalized_median_discrepancy:6.3f}   "
                    f"{result.observed_skew:+7.3f}/{result.predicted_skew:+7.3f}"
                )
            if m == final_m:
                final_results = results
        conditional_ok, reasons = prediction_status(final_results)
        status = uniform_ok and conditional_ok
        if prediction == "theorem":
            baseline_ok = status
        lines.append(f"prediction gate: {'PASS' if status else 'RED'}")
        if reasons:
            lines.extend(f"  RED reason: {reason}" for reason in reasons)

    negative_controls_ok = True
    if set(predictions) >= {"theorem", "flip-sign", "mu-power"}:
        mutation_statuses = {}
        for prediction in ("flip-sign", "mu-power"):
            result = conditional_results(final_samples, final_m, mu_c, stable_sample, prediction)
            mutation_statuses[prediction] = prediction_status(result)[0] and uniform_ok
        negative_controls_ok = not any(mutation_statuses.values())
        lines.extend(
            [
                "",
                "Mutation sensitivity",
                "--------------------",
                "flip-sign substitutes +mu_C^(-1-1/alpha)t^(1/alpha)S_alpha.",
                "mu-power substitutes -mu_C^(-1/alpha)t^(1/alpha)S_alpha.",
                "negative controls: " + ("PASS (both went RED)" if negative_controls_ok else "RED"),
            ]
        )

    # The runtime deliberately does not go into the report file. It varies between
    # runs, so recording it there would make the committed artifact differ from the
    # one a reader regenerates, and following REPRODUCE.md would break SHA256SUMS.
    lines.extend(["", f"OVERALL = {'PASS' if baseline_ok and negative_controls_ok else 'RED'}"])
    return "\n".join(lines) + "\n", baseline_ok and negative_controls_ok


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=SEED)
    parser.add_argument("--calibration-samples", type=int, default=3_000_000)
    parser.add_argument("--layer-samples", type=int, default=30_000)
    parser.add_argument("--stable-samples", type=int, default=1_000_000)
    parser.add_argument("--ladder", type=int, nargs="+", default=DEFAULT_LADDER)
    parser.add_argument(
        "--prediction",
        choices=("all", "theorem", "flip-sign", "mu-power"),
        default="all",
    )
    parser.add_argument(
        "--output",
        default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "critical_gibbs_geometry_check.txt"),
        help="artifact path relative to the paper directory, or - for stdout only",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    started = time.perf_counter()
    seed_sequence = np.random.SeedSequence(args.seed)
    calibration_seed, layer_seed, stable_seed = seed_sequence.spawn(3)
    calibration_rng = np.random.default_rng(calibration_seed)
    layer_rng = np.random.default_rng(layer_seed)
    stable_rng = np.random.default_rng(stable_seed)

    calibration_sampler = LetterSampler(
        calibration_rng, ALPHA, cap=max(MU_CAPS), batch_size=250_000
    )
    calibration = calibration_sampler.take(args.calibration_samples).astype(float)
    mu_rows: list[tuple[int, float, float, float, float]] = []
    mu_c = math.nan
    for cap in MU_CAPS:
        capped = np.minimum(calibration, cap)
        capped_mean = float(np.mean(capped))
        correction = K_C / (ALPHA - 1.0) * cap ** (1.0 - ALPHA)
        estimate = capped_mean + correction
        standard_error = float(np.std(capped, ddof=1) / math.sqrt(len(capped)))
        mu_rows.append((cap, capped_mean, correction, estimate, standard_error))
        if cap == MU_SELECTED_CAP:
            mu_c = estimate

    ladder = tuple(sorted(set(args.ladder)))
    layer_sampler = LetterSampler(
        layer_rng, ALPHA, cap=max(ladder) + 1, batch_size=250_000
    )
    layer_rows: list[tuple[int, LayerSamples, float, list[float]]] = []
    for m in ladder:
        samples = sample_layer(layer_rng, layer_sampler, m, args.layer_samples)
        scaled_cost = samples.cost / m
        ks = empirical_ks_uniform(scaled_cost)
        discrepancies = [
            float(np.mean(scaled_cost <= point) - point) for point in (0.25, 0.50, 0.75)
        ]
        layer_rows.append((m, samples, ks, discrepancies))

    stable_sample = sample_spectrally_positive_stable(stable_rng, ALPHA, args.stable_samples)
    predictions = (
        ("theorem", "flip-sign", "mu-power")
        if args.prediction == "all"
        else (args.prediction,)
    )
    elapsed = time.perf_counter() - started
    report, passed = format_report(
        args.seed,
        args.calibration_samples,
        mu_rows,
        mu_c,
        layer_rows,
        stable_sample,
        predictions,
        elapsed,
    )
    if args.output == "-":
        sys.stdout.write(report)
    else:
        output_path = Path(args.output)
        output_path.write_text(report, encoding="ascii", newline="\n")
        sys.stdout.write(report)
        print(f"wrote {output_path}")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
