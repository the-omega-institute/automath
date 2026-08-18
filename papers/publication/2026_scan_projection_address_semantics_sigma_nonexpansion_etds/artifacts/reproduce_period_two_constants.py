#!/usr/bin/env python3
"""Reproduce the period-two constants from the example's transition data.

The only mathematical data encoded below are the transition matrix K,
the hole/safe-state split, and the two cyclic classes stated in
sec_open_system_resonance.tex.  All stationary, spectral, amplitude,
Renyi-rate, and collision-constant values are derived from those data.
"""

from dataclasses import dataclass

import sympy as sp


STATES = ("a", "b", "c", "h")
K = sp.Matrix(
    [
        [0, sp.Rational(1, 3), sp.Rational(1, 3), sp.Rational(1, 3)],
        [sp.Rational(1, 2), 0, 0, sp.Rational(1, 2)],
        [sp.Rational(1, 4), 0, 0, sp.Rational(3, 4)],
        [sp.Rational(1, 4), sp.Rational(1, 4), sp.Rational(1, 4), sp.Rational(1, 4)],
    ]
)
HOLE = (3,)
SAFE = tuple(index for index in range(len(STATES)) if index not in HOLE)

# Indices here are local to the safe-state ordering (a, b, c).
CYCLIC_CLASSES = ((0,), (1, 2))


@dataclass(frozen=True)
class PerronData:
    rho: sp.Expr
    right: sp.Matrix
    left: sp.Matrix


def stationary_distribution(transition: sp.Matrix) -> sp.Matrix:
    """Solve pi^T K = pi^T and sum(pi) = 1 exactly."""
    variables = sp.symbols(f"p0:{transition.rows}")
    column = sp.Matrix(variables)
    equations = list((transition.T - sp.eye(transition.rows)) * column)
    equations.append(sum(variables) - 1)
    solutions = sp.linsolve(equations, variables)
    solution = next(iter(solutions))
    return sp.Matrix([sp.simplify(value) for value in solution])


def killed_entrywise_power(transition: sp.Matrix, s: int) -> sp.Matrix:
    """Construct B_s from the safe-to-safe entries of K."""
    killed = transition.extract(SAFE, SAFE)
    return killed.applyfunc(lambda value: sp.simplify(value**s))


def orient_positive(vector: sp.Matrix) -> sp.Matrix:
    if all(entry.is_positive for entry in vector):
        return vector
    if all((-entry).is_positive for entry in vector):
        return -vector
    raise ValueError(f"could not orient eigenvector positively: {vector}")


def perron_data(matrix: sp.Matrix) -> PerronData:
    """Find positive left/right Perron vectors and normalize left^T right=1."""
    positive_eigenvalues = [
        sp.simplify(value)
        for value in matrix.eigenvals()
        if value.is_real and value.is_positive
    ]
    if len(positive_eigenvalues) != 1:
        raise ValueError(f"expected one positive eigenvalue, got {positive_eigenvalues}")

    rho = positive_eigenvalues[0]
    right = orient_positive((matrix - rho * sp.eye(matrix.rows)).nullspace()[0])
    left = orient_positive((matrix.T - rho * sp.eye(matrix.rows)).nullspace()[0])
    left = sp.simplify(1 / left.dot(right)) * left

    assert (matrix * right - rho * right).applyfunc(sp.simplify).is_zero_matrix
    assert (matrix.T * left - rho * left).applyfunc(sp.simplify).is_zero_matrix
    assert sp.simplify(left.dot(right)) == 1
    return PerronData(rho=rho, right=right, left=left)


def cyclic_coefficient(
    initial_weights: sp.Matrix,
    perron: PerronData,
    phase: int,
) -> sp.Expr:
    """Evaluate eq:cyclic-coefficient with v=1 from its class sums."""
    period = len(CYCLIC_CLASSES)
    total = sp.S.Zero
    for class_index, source_class in enumerate(CYCLIC_CLASSES):
        target_class = CYCLIC_CLASSES[(class_index + phase) % period]
        source_weight = sum(
            initial_weights[i] * perron.right[i] for i in source_class
        )
        target_weight = sum(perron.left[j] for j in target_class)
        total += source_weight * target_weight
    return sp.simplify(period * total)


def phase_blind_coefficient(
    initial_weights: sp.Matrix,
    perron: PerronData,
) -> sp.Expr:
    """Use only the rank-one Perron projection, ignoring cyclic projectors."""
    return sp.simplify(
        initial_weights.dot(perron.right) * sum(perron.left)
    )


def sqrt_denominator_form(value: sp.Expr, radicand: int) -> str | None:
    """Format q/sqrt(n) when SymPy has rationalized it to q*sqrt(n)/n."""
    radical = sp.sqrt(radicand)
    coefficient = sp.simplify(value * radical)
    if not coefficient.is_Rational:
        return None
    numerator, denominator = sp.fraction(coefficient)
    if denominator == 1:
        return f"{numerator}/sqrt({radicand})"
    return f"{numerator}/({denominator}*sqrt({radicand}))"


def stationary_denominator_sqrt_form(
    value: sp.Expr,
    stationary_denominator: int,
    s: int,
    radicand: int,
) -> str | None:
    """Express an amplitude over pi's common denominator to the power s."""
    denominator = stationary_denominator**s
    numerator = sp.simplify(value * denominator * sp.sqrt(radicand))
    if not numerator.is_Integer:
        return None
    return f"{numerator}/({denominator}*sqrt({radicand}))"


def main() -> None:
    assert all(sp.simplify(sum(K.row(i)) - 1) == 0 for i in range(K.rows))
    pi = stationary_distribution(K)
    assert ((K.T * pi) - pi).applyfunc(sp.simplify).is_zero_matrix
    assert sp.simplify(sum(pi) - 1) == 0
    pi_denominator = sp.ilcm(*[sp.denom(value) for value in pi])

    spectral = {}
    amplitudes = {}
    blind_amplitudes = {}
    for s in (1, 2):
        matrix = killed_entrywise_power(K, s)
        perron = perron_data(matrix)
        initial_weights = sp.Matrix([pi[index] ** s for index in SAFE])
        phase_values = tuple(
            cyclic_coefficient(initial_weights, perron, phase)
            for phase in range(len(CYCLIC_CLASSES))
        )
        blind_value = phase_blind_coefficient(initial_weights, perron)

        # Averaging the cyclic projections removes their phase labels and
        # leaves precisely the ordinary rank-one Perron projection.
        assert sp.simplify(blind_value - sum(phase_values) / len(phase_values)) == 0
        spectral[s] = perron.rho
        amplitudes[s] = phase_values
        blind_amplitudes[s] = blind_value

    phase_constants = tuple(
        sp.factor(amplitudes[2][phase] / amplitudes[1][phase] ** 2)
        for phase in range(len(CYCLIC_CLASSES))
    )
    pair_rate_argument = sp.simplify(spectral[1] ** 2 / spectral[2])
    pair_rate = sp.log(pair_rate_argument)

    blind_constant = sp.factor(blind_amplitudes[2] / blind_amplitudes[1] ** 2)
    blind_by_phase = (blind_constant,) * len(CYCLIC_CLASSES)

    print("Input transition data from sec_open_system_resonance.tex")
    print(f"states = {STATES}")
    print(f"safe states = {tuple(STATES[index] for index in SAFE)}")
    print(f"cyclic classes = {CYCLIC_CLASSES}")
    print(f"pi = {tuple(pi)}")
    print()

    print("Phase-resolved calculation")
    for s in (1, 2):
        print(f"rho_{s} = {spectral[s]}")
        for phase, value in enumerate(amplitudes[s]):
            denominator_form = stationary_denominator_sqrt_form(
                value, pi_denominator, s, 5
            )
            if denominator_form:
                print(f"A_{s},{phase}(1) = {denominator_form} [simplified: {value}]")
            else:
                print(f"A_{s},{phase}(1) = {value}")
    for phase, value in enumerate(phase_constants):
        denominator_form = sqrt_denominator_form(value, 5)
        if denominator_form:
            print(f"c_2,{phase} = {denominator_form} [simplified: {value}]")
        else:
            print(f"c_2,{phase} = {value}")
    print(f"h_2,H = {pair_rate} = log({sqrt_denominator_form(pair_rate_argument, 5)})")
    print(
        "phase-resolved constants distinct: "
        f"{sp.simplify(phase_constants[0] - phase_constants[1]) != 0}"
    )
    print(f"decimal c_2,0 = {sp.N(phase_constants[0], 10)}")
    print(f"decimal c_2,1 = {sp.N(phase_constants[1], 10)}")
    print()

    print("Phase-blind control (rank-one Perron projection only)")
    for s in (1, 2):
        print(f"phase-blind A_{s}(1) = {blind_amplitudes[s]}")
    print(f"phase-blind c_2 = {blind_constant}")
    print(f"decimal phase-blind c_2 = {sp.N(blind_constant, 10)}")
    print(
        "phase-blind phase 0 = phase-blind phase 1: "
        f"{sp.simplify(blind_by_phase[0] - blind_by_phase[1]) == 0}"
    )


if __name__ == "__main__":
    main()
