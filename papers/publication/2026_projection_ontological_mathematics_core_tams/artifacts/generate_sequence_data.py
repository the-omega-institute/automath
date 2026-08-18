"""Generate exact collision moments and finite-window recurrence checks."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
from pathlib import Path

import numpy as np
import sympy as sp


RECURRENCES = {
    9: (9, (2, 62, 386, 2819, 62, 900, -450)),
    10: (11, (2, 96, 830, 7945, 2, 1852, -830, 4, -4)),
    11: (11, (2, 153, 1740, 21249, -9432, -86213, -1484, -18348, 9174)),
    12: (15, (2, 243, 3608, 56447, -61236, -667319, 3608, -9582, 61242, 15404, -7216, 8, -8)),
    13: (13, (2, 388, 7414, 148038, -317916, -4165856, 136252, 1565891, 318938, 289380, -144690)),
    14: (15, (2, 621, 15140, 385463, -1443744, -22761161, 15140, -2116566, 1443750, 63044, -30280, 8, -8)),
    15: (13, (2, 1000, 30766, 994458, -6188172, -119408756, 8289820, 134208623, 6186122, 16637076, -8318538)),
    16: (15, (2, 1611, 62312, 2559407, -24862788, -585266591, 62312, -44606766, 24862794, 255692, -124624, 8, -8)),
    17: (15, (2, 2599, 125872, 6569850, -96034590, -2764163954, -643026032, -15022392733, 769974566, 15329386299, 642908352, 1347896340, -673948170)),
}


def fibonacci_through(n: int) -> list[int]:
    values = [0, 1]
    while len(values) <= n:
        values.append(values[-1] + values[-2])
    return values


def residue_counts(m: int) -> np.ndarray:
    fib = fibonacci_through(m + 2)
    modulus = fib[m + 2]
    counts = np.zeros(modulus, dtype=np.uint64)
    counts[0] = 1
    for i in range(1, m + 1):
        counts += np.roll(counts, fib[i + 1])
    return counts


def moments(counts: np.ndarray) -> dict[int, int]:
    frequencies = np.bincount(counts.astype(np.int64))
    return {
        q: sum(int(frequency) * value**q for value, frequency in enumerate(frequencies))
        for q in RECURRENCES
    }


def recurrence_checks(sequences: dict[int, list[int]], m_max: int) -> dict[str, object]:
    checks: dict[str, object] = {}
    for q, (m0, coefficients) in RECURRENCES.items():
        sequence = sequences[q]
        mismatches = []
        for m in range(m0, m_max + 1):
            predicted = sum(c * sequence[m - i] for i, c in enumerate(coefficients, 1))
            if sequence[m] != predicted:
                mismatches.append({"m": m, "actual": sequence[m], "predicted": predicted})

        order = len(coefficients)
        hankel = sp.Matrix([[sequence[i + j] for j in range(order)] for i in range(order)])
        checks[str(q)] = {
            "order": order,
            "valid_from": m0,
            "verified_through": m_max,
            "mismatches": mismatches,
            "initial_hankel_rank": int(hankel.rank()),
            "initial_hankel_determinant": int(hankel.det()),
            "lower_order_excluded_by_initial_data": int(hankel.rank()) == order,
        }
    return checks


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m-max", type=int, default=26)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_name("sequence_data_q9_17.json"),
    )
    args = parser.parse_args()
    if args.m_max < 26:
        raise SystemExit("m-max must be at least 26 for the archival checks")

    sequences = {q: [] for q in RECURRENCES}
    moduli = []
    for m in range(args.m_max + 1):
        counts = residue_counts(m)
        moduli.append(int(counts.size))
        for q, value in moments(counts).items():
            sequences[q].append(value)
        print(f"m={m:2d} modulus={counts.size}", flush=True)

    payload = {
        "schema": 1,
        "definition": "S_q(m)=sum_r c_m(r)^q, c_m(r)=#{omega: sum omega_i F_(i+1)=r mod F_(m+2)}",
        "m_range": [0, args.m_max],
        "q_range": [9, 17],
        "moduli": moduli,
        "sequences": {str(q): values for q, values in sequences.items()},
        "recurrences": {
            str(q): {"valid_from": m0, "coefficients": list(coefficients)}
            for q, (m0, coefficients) in RECURRENCES.items()
        },
        "finite_window_checks": recurrence_checks(sequences, args.m_max),
        "environment": {
            "python": platform.python_version(),
            "numpy": np.__version__,
            "sympy": sp.__version__,
        },
        "status": "Direct data and finite-window checks only; not an all-m recurrence proof.",
    }
    encoded = (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("ascii")
    args.output.write_bytes(encoded)
    print(f"wrote={args.output}")
    print(f"sha256={hashlib.sha256(encoded).hexdigest()}")


if __name__ == "__main__":
    main()
