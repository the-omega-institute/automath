"""
Generate the LaTeX table of Frobenius traces for the Prym threefold Q.

The regular S_4-closure is counted fibre by fibre from its decomposition and
inertia groups.  The trace obtained from the full isogeny decomposition is
checked independently against a_1(Y)-a_1(E_res), where Y=X/C_4.  The same
double-coset counter is also checked against the explicit models of
E=X/S_3, E_res=X/D_4, and X_A=X/A_4.
"""
import argparse
import itertools
import math
import os
import re
from fractions import Fraction


def is_prime(n):
    if n < 2:
        return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0:
            return False
    return True


def legendre(a, p):
    if a % p == 0:
        return 0
    return 1 if pow(a % p, (p - 1) // 2, p) == 1 else -1


def count_E37(p):
    count = 0
    for x in range(p):
        rhs = (4 * pow(x, 3, p) - 4 * x + 1) % p
        symbol = legendre(rhs, p)
        if symbol == 0:
            count += 1
        elif symbol == 1:
            count += 2
    return count + 1


def count_Eres(p):
    count = 0
    for x in range(p):
        rhs = (4 * pow(x, 3, p) - 4 * pow(x, 2, p) - 36 * x + 37) % p
        symbol = legendre(rhs, p)
        if symbol == 0:
            count += 1
        elif symbol == 1:
            count += 2
    return count + 1


def count_XA(p):
    count = 0
    for y in range(p):
        fval = (-y * (y - 1) * cubic_value(p, y)) % p
        symbol = legendre(fval, p)
        if symbol == 0:
            count += 1
        elif symbol == 1:
            count += 2
    return count + 1


def cubic_value(p, y):
    return (256 * pow(y, 3, p) + 411 * pow(y, 2, p) + 165 * y + 32) % p


def quartic_coefficients(p, y):
    return ((y * (y + 1)) % p, 1, (-(2 * y + 1)) % p, -1, 1)


def count_quartic_roots(p, y):
    a0, a1, a2, a3, a4 = quartic_coefficients(p, y)
    return sum(
        1
        for lam in range(p)
        if (a4 * pow(lam, 4, p) + a3 * pow(lam, 3, p)
            + a2 * pow(lam, 2, p) + a1 * lam + a0) % p == 0
    )


def has_quadratic_factor(p, y):
    a0, a1, a2, a3, _ = quartic_coefficients(p, y)
    for q1 in range(p):
        for q0 in range(p):
            x4_1 = (-q1**3 + 2 * q1 * q0) % p
            x4_0 = (-q1 * q1 * q0 + q0 * q0) % p
            x3_1 = (q1 * q1 - q0) % p
            x3_0 = (q1 * q0) % p
            remainder_1 = (x4_1 + a3 * x3_1 - a2 * q1 + a1) % p
            remainder_0 = (x4_0 + a3 * x3_0 - a2 * q0 + a0) % p
            if remainder_1 == 0 and remainder_0 == 0:
                return True
    return False


def compose(left, right):
    return tuple(left[right[i]] for i in range(4))


IDENTITY = (0, 1, 2, 3)
TRANSPOSITION = (1, 0, 2, 3)
COMPLEMENTARY_TRANSPOSITION = (0, 1, 3, 2)
THREE_CYCLE = (1, 2, 0, 3)
FOUR_CYCLE = (1, 2, 3, 0)
DOUBLE_TRANSPOSITION = (1, 0, 3, 2)
FOUR_CYCLE_REFLECTION = (0, 3, 2, 1)
S4 = tuple(itertools.permutations(range(4)))


def generated_subgroup(*generators):
    subgroup = {IDENTITY}
    changed = True
    while changed:
        changed = False
        for left in tuple(subgroup):
            for right in generators + tuple(subgroup):
                product = compose(left, right)
                if product not in subgroup:
                    subgroup.add(product)
                    changed = True
    return frozenset(subgroup)


I_TRANS = generated_subgroup(TRANSPOSITION)
I_C4 = generated_subgroup(FOUR_CYCLE)
H_TRIVIAL = frozenset({IDENTITY})
H_S3 = frozenset(g for g in S4 if g[3] == 3)
H_A4 = frozenset(
    g for g in S4
    if sum(g[i] > g[j] for i in range(4) for j in range(i + 1, 4)) % 2 == 0
)
H_C4 = I_C4
H_D4 = generated_subgroup(FOUR_CYCLE, FOUR_CYCLE_REFLECTION)
H_FINITE_NONSPLIT = generated_subgroup(TRANSPOSITION, COMPLEMENTARY_TRANSPOSITION)


GAUSSIAN_ZERO = (Fraction(0), Fraction(0))
GAUSSIAN_ONE = (Fraction(1), Fraction(0))


def gaussian(real=0, imag=0):
    return Fraction(real), Fraction(imag)


def gaussian_add(left, right):
    return left[0] + right[0], left[1] + right[1]


def gaussian_multiply(left, right):
    return (
        left[0] * right[0] - left[1] * right[1],
        left[0] * right[1] + left[1] * right[0],
    )


def gaussian_scale(value, scalar):
    scalar = Fraction(scalar)
    return value[0] * scalar, value[1] * scalar


def series_add(*series, order):
    result = [GAUSSIAN_ZERO for _ in range(order + 1)]
    for summand in series:
        for degree, coefficient in enumerate(summand[:order + 1]):
            result[degree] = gaussian_add(result[degree], coefficient)
    return result


def series_multiply(left, right, order):
    result = [GAUSSIAN_ZERO for _ in range(order + 1)]
    for left_degree, left_coefficient in enumerate(left):
        for right_degree, right_coefficient in enumerate(right):
            degree = left_degree + right_degree
            if degree <= order:
                product = gaussian_multiply(left_coefficient, right_coefficient)
                result[degree] = gaussian_add(result[degree], product)
    return result


def series_power(series, exponent, order):
    result = [GAUSSIAN_ONE] + [GAUSSIAN_ZERO for _ in range(order)]
    for _ in range(exponent):
        result = series_multiply(result, series, order)
    return result


def series_shift(series, degree, scalar, order):
    result = [GAUSSIAN_ZERO for _ in range(order + 1)]
    for index, coefficient in enumerate(series):
        if index + degree <= order:
            result[index + degree] = gaussian_scale(coefficient, scalar)
    return result


def branch_equation_residual(branch, order=7):
    square = series_power(branch, 2, order)
    cube = series_power(branch, 3, order)
    fourth = series_power(branch, 4, order)
    constant = [GAUSSIAN_ONE] + [GAUSSIAN_ZERO for _ in range(order)]
    constant[4] = GAUSSIAN_ONE
    return series_add(
        fourth,
        series_shift(cube, 2, -1, order),
        series_shift(square, 0, -2, order),
        series_shift(square, 4, -1, order),
        series_shift(branch, 6, 1, order),
        constant,
        order=order,
    )


def format_gaussian(value):
    real, imag = value
    if imag == 0:
        return str(real)
    if real == 0:
        return f"{imag}*i"
    sign = "+" if imag > 0 else "-"
    return f"{real}{sign}{abs(imag)}*i"


BRANCH_EXPANSIONS = (
    (
        "L=1, positive t coefficient",
        (gaussian(1), gaussian(Fraction(1, 2)), gaussian(Fraction(1, 4)),
         gaussian(Fraction(7, 64)), gaussian(Fraction(37, 128)),
         gaussian(Fraction(-729, 4096))),
    ),
    (
        "L=1, negative t coefficient",
        (gaussian(1), gaussian(Fraction(-1, 2)), gaussian(Fraction(1, 4)),
         gaussian(Fraction(-7, 64)), gaussian(Fraction(37, 128)),
         gaussian(Fraction(729, 4096))),
    ),
    (
        "L=-1, positive i*t coefficient",
        (gaussian(-1), gaussian(0, Fraction(1, 2)), gaussian(Fraction(1, 4)),
         gaussian(0, Fraction(-7, 64)), gaussian(Fraction(-37, 128)),
         gaussian(0, Fraction(-729, 4096))),
    ),
    (
        "L=-1, negative i*t coefficient",
        (gaussian(-1), gaussian(0, Fraction(-1, 2)), gaussian(Fraction(1, 4)),
         gaussian(0, Fraction(7, 64)), gaussian(Fraction(-37, 128)),
         gaussian(0, Fraction(729, 4096))),
    ),
)


def verify_branch_expansions():
    rational_branches = 0
    for name, branch in BRANCH_EXPANSIONS:
        residual = branch_equation_residual(branch)
        first_failure = next(
            ((degree, coefficient) for degree, coefficient in enumerate(residual)
             if coefficient != GAUSSIAN_ZERO),
            None,
        )
        assert first_failure is None, (
            f"branch expansion failed for {name}: coefficient of "
            f"t^{first_failure[0]} is {format_gaussian(first_failure[1])}"
        )
        rational_branches += all(coefficient[1] == 0 for coefficient in branch)
    assert rational_branches == 2, (
        f"branch field check failed: expected 2 rational branches and 2 requiring i, "
        f"found {rational_branches} rational branches"
    )


def rational_double_cosets(left_subgroup, inertia, frobenius):
    orbit_id = {}
    orbits = []
    for start in S4:
        if start in orbit_id:
            continue
        orbit = {
            compose(compose(left, start), right)
            for left in left_subgroup
            for right in inertia
        }
        index = len(orbits)
        for element in orbit:
            orbit_id[element] = index
        orbits.append(orbit)
    return sum(
        orbit_id[compose(next(iter(orbit)), frobenius)] == index
        for index, orbit in enumerate(orbits)
    )


def unramified_frobenius(p, y, root_count):
    if root_count == 4:
        return IDENTITY
    if root_count == 2:
        return TRANSPOSITION
    if root_count == 1:
        return THREE_CYCLE
    return DOUBLE_TRANSPOSITION if has_quadratic_factor(p, y) else FOUR_CYCLE


def fibre_data(p, y):
    root_count = count_quartic_roots(p, y)
    if y in (0, 1) or cubic_value(p, y) == 0:
        frobenius = IDENTITY if root_count == 3 else COMPLEMENTARY_TRANSPOSITION
        return I_TRANS, frobenius, root_count
    return H_TRIVIAL, unramified_frobenius(p, y, root_count), root_count


def branch_fibre_row(p, label, inertia, frobenius):
    decomposition = generated_subgroup(*(tuple(inertia) + (frobenius,)))
    return {
        "point": label,
        "inertia": inertia,
        "decomposition": decomposition,
        "residue_degree": len(decomposition) // len(inertia),
        "rational_points": rational_double_cosets(H_TRIVIAL, inertia, frobenius),
    }


def rational_branch_fibres(p):
    rows = []
    for y in range(p):
        if y in (0, 1) or cubic_value(p, y) == 0:
            inertia, frobenius, _ = fibre_data(p, y)
            rows.append(branch_fibre_row(p, f"y={y}", inertia, frobenius))
    infinity_frobenius = IDENTITY if p % 4 == 1 else FOUR_CYCLE_REFLECTION
    rows.append(branch_fibre_row(p, "infinity", I_C4, infinity_frobenius))
    return rows


def verify_boundary_regressions():
    # p=7: no rational root of c and p=3 mod 4, so infinity contributes 0.
    p7 = {row["point"]: row["rational_points"] for row in rational_branch_fibres(7)}
    assert p7 == {"y=0": 12, "y=1": 12, "infinity": 0}, f"p=7 boundary fibres: {p7}"

    # p=13: the rational c-root is inert, while p=1 mod 4 gives 6 at infinity.
    p13 = {row["point"]: row["rational_points"] for row in rational_branch_fibres(13)}
    assert p13 == {"y=0": 12, "y=1": 12, "y=11": 0, "infinity": 6}, (
        f"p=13 boundary fibres: {p13}"
    )

    # p=19: the rational c-root is inert and p=3 mod 4 gives 0 at infinity.
    p19 = {row["point"]: row["rational_points"] for row in rational_branch_fibres(19)}
    assert p19 == {"y=0": 12, "y=1": 12, "y=13": 0, "infinity": 0}, (
        f"p=19 boundary fibres: {p19}"
    )

    # p=89: c has three rational roots, exactly one residual quadratic splits, and infinity gives 6.
    p89 = {row["point"]: row["rational_points"] for row in rational_branch_fibres(89)}
    assert p89 == {"y=0": 12, "y=1": 12, "y=9": 0, "y=26": 0, "y=59": 12, "infinity": 6}, (
        f"p=89 boundary fibres: {p89}"
    )


def subgroup_name(subgroup):
    names = {
        I_TRANS: "C2",
        I_C4: "C4",
        H_FINITE_NONSPLIT: "C2 x C2",
        H_D4: "D4",
    }
    return names.get(subgroup, f"group of order {len(subgroup)}")


def print_branch_diagnostics(p):
    if not is_prime(p) or p in BAD_PRIMES:
        raise SystemExit(f"diagnostic prime must be a good prime, got {p}")
    print(f"Rational branch fibres for p={p}")
    print("point\tinertia\tdecomposition\tresidue degree\trational points")
    for row in rational_branch_fibres(p):
        print(
            f"{row['point']}\t{subgroup_name(row['inertia'])}\t"
            f"{subgroup_name(row['decomposition'])}\t{row['residue_degree']}\t"
            f"{row['rational_points']}"
        )


def count_quotient(p, subgroup):
    count = 0
    for y in range(p):
        inertia, frobenius, _ = fibre_data(p, y)
        count += rational_double_cosets(subgroup, inertia, frobenius)
    infinity_frobenius = IDENTITY if p % 4 == 1 else FOUR_CYCLE_REFLECTION
    count += rational_double_cosets(subgroup, I_C4, infinity_frobenius)
    return count


def corrected_X_count(p):
    n_split = 0
    n_c = 0
    for y in range(p):
        roots = count_quartic_roots(p, y)
        if y not in (0, 1) and cubic_value(p, y) != 0 and roots == 4:
            n_split += 1
        elif cubic_value(p, y) == 0 and roots == 3:
            n_c += 1
    return 24 * n_split + 12 * (2 + n_c) + 6 * (p % 4 == 1)


BAD_PRIMES = {2, 3, 31, 37}
# Regression fixture only: pins published values and is not part of the derivation.
# Genuine checks are the quotient self-match, divisibility, Weil bound, and Y = X/C_4 cross-check.
REGRESSION_FIXTURE_Q_TRACES = {
    5: -5, 7: -2, 11: -3, 13: -2, 17: -5, 19: 2, 23: -3,
    29: -3, 41: 1, 43: -10, 47: -7, 53: -7, 59: 9, 61: -8,
    67: -7, 71: -5, 73: 3, 79: 6, 83: -5, 89: -4, 97: 8,
    101: -3, 103: -20, 107: 10, 109: 6, 113: 9,
}


def generate_results():
    primes = [p for p in range(5, 120) if is_prime(p) and p not in BAD_PRIMES]
    results = []
    for index, p in enumerate(primes):
        model_counts = {
            "E": count_E37(p),
            "E_res": count_Eres(p),
            "X_A": count_XA(p),
        }
        quotient_counts = {
            "E": count_quotient(p, H_S3),
            "E_res": count_quotient(p, H_D4),
            "X_A": count_quotient(p, H_A4),
        }
        assert quotient_counts == model_counts, (
            f"p={p}: quotient self-match failed: "
            f"group={quotient_counts}, models={model_counts}"
        )

        total_X = corrected_X_count(p)
        group_total_X = count_quotient(p, H_TRIVIAL)
        assert total_X == group_total_X, (
            f"p={p}: corrected formula gives {total_X}, group method gives {group_total_X}"
        )

        a1_XA = p + 1 - model_counts["X_A"]
        a1_Eres = p + 1 - model_counts["E_res"]
        a1_E37 = p + 1 - model_counts["E"]
        a1_X = p + 1 - total_X
        difference = a1_X - a1_XA - 2 * a1_Eres - 3 * a1_E37
        assert difference % 3 == 0, f"p={p}: difference={difference} is not divisible by 3"
        a1_Q = difference // 3

        count_Y = count_quotient(p, H_C4)
        a1_Q_from_Y = (p + 1 - count_Y) - a1_Eres
        assert a1_Q == a1_Q_from_Y, (
            f"p={p}: decomposition gives {a1_Q}, Y/E_res gives {a1_Q_from_Y}"
        )
        assert a1_Q == REGRESSION_FIXTURE_Q_TRACES[p], (
            f"p={p}: computed a_1(Q)={a1_Q}, regression fixture {REGRESSION_FIXTURE_Q_TRACES[p]}"
        )
        assert abs(a1_Q) <= 6 * math.sqrt(p), f"p={p}: Weil bound failed for a_1(Q)={a1_Q}"

        results.append((p, a1_XA, a1_Eres, a1_E37, a1_Q))
        if (index + 1) % 10 == 0:
            print(f"  progress: {index + 1}/{len(primes)} primes computed")
    return results


def table_text(results):
    lines = [
        "% Auto-generated by scripts/generate_Q_traces_table.py",
        r"\begin{tabular}{r|rrrr}",
        r"$p$ & $a_1(\Jac(X_A))$ & $a_1(E_{\mathrm{res}})$ & $a_1(E)$ & $a_1(Q)$ \\ \hline",
    ]
    for p, a1_XA, a1_Eres, a1_E37, a1_Q in results[:15]:
        lines.append(f"${p}$ & ${a1_XA}$ & ${a1_Eres}$ & ${a1_E37}$ & ${a1_Q}$ \\\\")
    lines.append(r"\end{tabular}")
    return "\n".join(lines) + "\n"


def paper_directory():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    return os.path.dirname(script_dir) if os.path.basename(script_dir) == "scripts" else script_dir


def verify_documented_proposition_number():
    expected_number = "6.11"
    aux_path = os.path.join(paper_directory(), "revised_main_flattened.aux")
    if not os.path.exists(aux_path):
        print(f"Numbering guard skipped: {aux_path} is absent.")
        return

    with open(aux_path, encoding="utf-8", errors="replace") as aux_file:
        aux_text = aux_file.read()
    match = re.search(r"\\newlabel\{prop:prym-traces\}\{\{([^}]*)\}", aux_text)
    assert match is not None, f"Numbering guard: prop:prym-traces is missing from {aux_path}"
    actual_number = match.group(1)
    assert actual_number == expected_number, (
        f"Numbering guard: prop:prym-traces resolves to {actual_number}, "
        f"but the reproducibility notes cite Proposition {expected_number}"
    )
    print(f"Numbering guard passed: prop:prym-traces resolves to {actual_number}.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--diagnose-prime",
        type=int,
        metavar="P",
        help="print decomposition data for the rational branch fibres at P",
    )
    args = parser.parse_args()
    verify_documented_proposition_number()
    verify_branch_expansions()
    verify_boundary_regressions()
    if args.diagnose_prime is not None:
        print_branch_diagnostics(args.diagnose_prime)
        return
    results = generate_results()
    paper_dir = paper_directory()
    output_paths = [
        os.path.join(paper_dir, "revised_prym_traces_table.tex"),
    ]
    output = table_text(results)
    for output_path in output_paths:
        with open(output_path, "w", encoding="ascii", newline="\n") as table_file:
            table_file.write(output)
        print(f"Table written to {output_path}")

    print(
        f"Computed {len(results)} primes; quotient self-matches, second Y/E_res trace route, "
        "divisibility, and Weil bounds all passed."
    )
    print(f"First 15 a_1(Q) values: {[row[4] for row in results[:15]]}")


if __name__ == "__main__":
    main()
