from __future__ import annotations

from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np


def add_poly(*polys: list[int]) -> list[int]:
    size = max(len(poly) for poly in polys)
    out = [0] * size
    for poly in polys:
        for idx, coeff in enumerate(poly):
            out[idx] += coeff
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def scale_poly(poly: list[int], factor: int) -> list[int]:
    return [factor * coeff for coeff in poly]


def shift_poly(poly: list[int], degree: int) -> list[int]:
    return [0] * degree + poly


def divide_by_y_plus_one(poly: list[int]) -> list[int]:
    desc = list(reversed(poly))
    quotient = [desc[0]]
    for coeff in desc[1:-1]:
        quotient.append(coeff - quotient[-1])
    remainder = desc[-1] - quotient[-1]
    if remainder != 0:
        raise ValueError("Polynomial is not divisible by y + 1.")
    return list(reversed(quotient))


def build_partition_polynomials(max_m: int) -> list[list[int]]:
    z = [
        [1],
        [1, 1],
        [1, 2, 1],
        [1, 3, 3, 1],
    ]
    for m in range(4, max_m + 1):
        z_prev = z[m - 1]
        z_prev2 = z[m - 2]
        z_prev3 = z[m - 3]
        z_prev4 = z[m - 4]
        term = add_poly(
            z_prev,
            z_prev2,
            scale_poly(shift_poly(z_prev2, 1), 2),
            scale_poly(z_prev3, -1),
            scale_poly(shift_poly(z_prev4, 1), -1),
            scale_poly(shift_poly(z_prev4, 2), -1),
        )
        z.append(term)
    return z


def polynomial_roots(poly: list[int]) -> np.ndarray:
    coeffs = np.array(list(reversed(poly)), dtype=np.float64)
    return np.roots(coeffs)


def zero_roots_with_exact_double_zero(poly: list[int]) -> np.ndarray:
    reduced = divide_by_y_plus_one(divide_by_y_plus_one(poly))
    roots = polynomial_roots(reduced)
    return np.concatenate([roots, np.array([-1.0 + 0.0j, -1.0 + 0.0j])])


def nearest_negative_real_zeros(poly: list[int], count: int) -> np.ndarray:
    roots = polynomial_roots(poly)
    candidates = sorted(
        (root.real for root in roots if abs(root.imag) < 1e-8 and -1.0 < root.real < 0.0),
        reverse=True,
    )
    if len(candidates) < count:
        raise ValueError("Not enough negative real zeros in the vacuum-edge window.")
    return np.array(candidates[:count], dtype=np.float64)


def spectral_roots(y_value: complex) -> np.ndarray:
    coeffs = np.array(
        [1.0, -1.0, -(2.0 * y_value + 1.0), 1.0, y_value * (y_value + 1.0)],
        dtype=np.complex128,
    )
    return np.roots(coeffs)


def dominant_gap(y_value: complex) -> float:
    moduli = np.sort(np.abs(spectral_roots(y_value)))[::-1]
    return float(moduli[0] - moduli[1])


def compute_y_sub() -> float:
    roots = np.roots([256.0, 411.0, 165.0, 32.0])
    real_roots = [root.real for root in roots if abs(root.imag) < 1e-10]
    if len(real_roots) != 1:
        raise ValueError("Expected a unique real root for the cubic branch polynomial.")
    return float(real_roots[0])


def draw_validation_figure(output_path: Path) -> None:
    y_sub = compute_y_sub()
    partition_polys = build_partition_polynomials(200)
    roots_80 = zero_roots_with_exact_double_zero(partition_polys[80])
    roots_120 = zero_roots_with_exact_double_zero(partition_polys[120])
    quantization_ms = [80, 120, 200]
    quantization_count = 4
    quantization_data = {
        m: -m * m * nearest_negative_real_zeros(partition_polys[m], quantization_count)
        for m in quantization_ms
    }
    k_values = np.arange(1, quantization_count + 1, dtype=np.float64)
    leading_quantization = 0.5 * np.pi**2 * (2.0 * k_values - 1.0) ** 2

    y_real = np.linspace(-1.6, 1.2, 1500)
    ordered_moduli = np.empty((y_real.size, 4), dtype=np.float64)
    for idx, value in enumerate(y_real):
        ordered_moduli[idx] = np.sort(np.abs(spectral_roots(value)))[::-1]

    x_min, x_max = -2.0, 1.2
    i_min, i_max = -0.5, 0.5

    plt.style.use("seaborn-v0_8-whitegrid")
    plt.rcParams["pdf.fonttype"] = 42
    plt.rcParams["ps.fonttype"] = 42
    fig, (ax_left, ax_center, ax_right) = plt.subplots(1, 3, figsize=(15.2, 4.8), constrained_layout=True)

    colors = ["#203864", "#287271", "#ee964b", "#b14923"]
    labels = [r"$|\lambda|_{(1)}$", r"$|\lambda|_{(2)}$", r"$|\lambda|_{(3)}$", r"$|\lambda|_{(4)}$"]
    for idx in range(4):
        ax_left.plot(y_real, ordered_moduli[:, idx], color=colors[idx], lw=1.7, label=labels[idx])
    for marker_x, marker_color, marker_label in [
        (y_sub, "#8f1d21", r"$y_{\mathrm{sub}}$"),
        (0.0, "#1b4332", r"$y=0$"),
        (1.0, "#6c584c", r"$y=1$"),
    ]:
        ax_left.axvline(marker_x, color=marker_color, lw=1.0, ls="--")
        ax_left.text(marker_x, 0.05, marker_label, color=marker_color, rotation=90, va="bottom", ha="right")
    ax_left.set_xlim(-1.6, 1.2)
    ax_left.set_ylim(0.0, 2.8)
    ax_left.set_xlabel(r"real fugacity $y$")
    ax_left.set_ylabel(r"ordered spectral moduli")
    ax_left.set_title("Real-axis modulus ordering")
    ax_left.legend(frameon=True, fontsize=9, loc="upper left")

    ax_center.axhline(0.0, color="#a8adb3", lw=0.9, zorder=0)
    ax_center.scatter(roots_80.real, roots_80.imag, s=18, color="#1d4e89", alpha=0.75, label=r"zeros of $Z_{80}$")
    ax_center.scatter(roots_120.real, roots_120.imag, s=14, color="#c44536", alpha=0.75, label=r"zeros of $Z_{120}$")
    ax_center.scatter([y_sub], [0.0], s=80, marker="D", color="#8f1d21", label=r"$y_{\mathrm{sub}}$")
    ax_center.scatter([0.0], [0.0], s=90, marker="*", color="#1b4332", label=r"$y=0$")
    ax_center.scatter([1.0], [0.0], s=55, marker="s", color="#6c584c", label=r"$y=1$")
    ax_center.scatter([-1.0], [0.0], s=70, marker="x", color="#111111", linewidths=1.7, label=r"exact double zero $y=-1$")
    ax_center.set_xlim(x_min, x_max)
    ax_center.set_ylim(i_min, i_max)
    ax_center.set_xlabel(r"$\Re y$")
    ax_center.set_ylabel(r"$\Im y$")
    ax_center.set_title("Finite-volume zero clouds")
    ax_center.legend(frameon=True, fontsize=8, loc="upper left")

    ax_right.plot(k_values, leading_quantization, color="#111111", lw=1.3, label=r"leading law $\frac{\pi^2}{2}(2k-1)^2$")
    offsets = [-0.10, 0.0, 0.10]
    quant_colors = ["#1d4e89", "#c44536", "#2a9d8f"]
    for offset, color, m in zip(offsets, quant_colors, quantization_ms):
        predicted = leading_quantization * (1.0 + 3.0 / (2.0 * m))
        ax_right.scatter(
            k_values + offset,
            quantization_data[m],
            s=34,
            color=color,
            label=rf"exact $-m^2y_{{m,k}}$, $m={m}$",
        )
        ax_right.scatter(
            k_values + offset,
            predicted,
            s=42,
            facecolors="none",
            edgecolors=color,
            linewidths=1.2,
            label="two-term asymptotic" if m == quantization_ms[0] else None,
        )
    ax_right.set_xlim(0.55, quantization_count + 0.45)
    ax_right.set_xlabel(r"zero index $k$")
    ax_right.set_ylabel(r"scaled edge position $-m^2y_{m,k}$")
    ax_right.set_title("Vacuum-edge quantization")
    ax_right.legend(frameon=True, fontsize=7.5, loc="upper left")

    fig.savefig(output_path, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    paper_dir = Path(__file__).resolve().parents[1]
    output = paper_dir / "figures" / "zero_locus_validation.pdf"
    draw_validation_figure(output)
    print(f"Saved validation figure to {output}")
