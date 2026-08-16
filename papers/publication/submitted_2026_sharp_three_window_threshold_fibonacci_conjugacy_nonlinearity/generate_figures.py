"""Generate the exact fiber-size distribution figure used by the paper."""

from collections import Counter
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


def fibonacci_through(index: int) -> list[int]:
    values = [0, 1]
    while len(values) <= index:
        values.append(values[-1] + values[-2])
    return values


def fiber_histogram(window: int) -> Counter[int]:
    fibonacci = fibonacci_through(window + 2)
    modulus = fibonacci[window + 2]
    fibers = [0] * modulus
    weights = [fibonacci[k + 1] for k in range(1, window + 1)]

    for word in range(1 << window):
        residue = sum(weight for bit, weight in enumerate(weights) if word & (1 << bit))
        fibers[residue % modulus] += 1

    return Counter(fibers)


def main() -> None:
    windows = (5, 8, 12)
    colors = ("#1565c0", "#00897b", "#c62828")
    figure, axes = plt.subplots(1, 3, figsize=(10.8, 3.35), constrained_layout=True)

    for axis, window, color in zip(axes, windows, colors):
        histogram = fiber_histogram(window)
        sizes = sorted(histogram)
        axis.bar(sizes, [histogram[size] for size in sizes], color=color, width=0.72)
        axis.set_title(rf"$m={window}$")
        axis.set_xlabel(r"fiber size $d_m(x)$")
        axis.set_xticks(sizes)
        axis.grid(axis="y", color="#d9d9d9", linewidth=0.6)

    axes[0].set_ylabel("number of residue classes")
    output = Path(__file__).resolve().parent / "figures_jpa" / "fig_fiber_distribution.pdf"
    output.parent.mkdir(parents=True, exist_ok=True)
    figure.savefig(output, bbox_inches="tight")
    plt.close(figure)


if __name__ == "__main__":
    main()
