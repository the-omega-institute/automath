"""Recompute the exact fold-pairing identities and discriminating controls.

The paper uses F_1 = 1, F_2 = 2.  At level m the m+1 distinct parts are
F_1,...,F_{m+1} (equivalently F_2,...,F_{m+2} in classical indexing), and
the fold modulus is M = F_{m+2}.  For their representation counts R_m,

    C(m)   = sum_{0 <= v < M} R_m(v) R_m(v + M),
    T_2(m) = sum_n R_m(n)^2,
    S_2(m) = T_2(m) + 2 C(m).

The substantive identity checked here is C(m) = S_2(m-2).
"""

from collections import Counter
import sys


MIN_M = 3
MAX_M = 18

FIBONACCI = [0, 1, 2]
while len(FIBONACCI) <= MAX_M + 3:
    FIBONACCI.append(FIBONACCI[-1] + FIBONACCI[-2])


def representation_counts(m):
    """Return counts for subsets of F_1,...,F_{m+1}."""
    counts = Counter({0: 1})
    for weight in FIBONACCI[1 : m + 2]:
        next_counts = Counter(counts)
        for value, multiplicity in counts.items():
            next_counts[value + weight] += multiplicity
        counts = next_counts
    return counts


def moments(m):
    counts = representation_counts(m)
    modulus = FIBONACCI[m + 2]
    folded = Counter()
    for value, multiplicity in counts.items():
        folded[value % modulus] += multiplicity
    s_2 = sum(multiplicity**2 for multiplicity in folded.values())
    t_2 = sum(multiplicity**2 for multiplicity in counts.values())
    cross = sum(
        counts.get(value, 0) * counts.get(value + modulus, 0)
        for value in range(modulus)
    )
    return s_2, t_2, cross


def main():
    values = {m: moments(m) for m in range(0, MAX_M + 1)}
    s_2 = {m: triple[0] for m, triple in values.items()}
    t_2 = {m: triple[1] for m, triple in values.items()}
    cross = {m: triple[2] for m, triple in values.items()}
    tested = list(range(MIN_M, MAX_M + 1))

    a_violations = [m for m in tested if cross[m] != s_2[m - 2]]
    b_violations = [
        m for m in tested if s_2[m] != t_2[m] + 2 * s_2[m - 2]
    ]
    controls = {
        "2 S_2(m-1)": [
            m for m in tested if s_2[m] != t_2[m] + 2 * s_2[m - 1]
        ],
        "2 S_2(m-3)": [
            m for m in tested if s_2[m] != t_2[m] + 2 * s_2[m - 3]
        ],
        "3 S_2(m-2)": [
            m for m in tested if s_2[m] != t_2[m] + 3 * s_2[m - 2]
        ],
    }

    print(f"Python {sys.version.split()[0]}; tested {MIN_M} <= m <= {MAX_M}")
    print(f"A violations: {len(a_violations)} {a_violations}")
    print(f"B violations: {len(b_violations)} {b_violations}")
    for label, failures in controls.items():
        print(f"control {label}: fails {len(failures)}/{len(tested)}")
    print(
        f"m = {MAX_M}: {s_2[MAX_M]} = {t_2[MAX_M]}"
        f" + 2 * {s_2[MAX_M - 2]}"
    )

    controls_discriminate = all(len(failures) == len(tested) for failures in controls.values())
    return 0 if not a_violations and not b_violations and controls_discriminate else 1


if __name__ == "__main__":
    raise SystemExit(main())
