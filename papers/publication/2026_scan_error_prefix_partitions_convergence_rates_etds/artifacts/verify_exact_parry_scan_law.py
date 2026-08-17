"""Numerical check of the exact Parry matrix law on the golden-mean example."""

from math import sqrt


def mat_vec(row, matrix, col):
    return sum(row[i] * sum(matrix[i][j] * col[j] for j in range(len(col)))
               for i in range(len(row)))


def main():
    lam = (1.0 + sqrt(5.0)) / 2.0
    a = 1.0 / lam

    # Refined ambiguous matrix from the golden-mean computation, in the order
    # (u,e_0,e_1,o_0,o_1).
    B = [
        [0.0, 1.0, 1.0, 0.0, 0.0],
        [0.0, 0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, 0.0, 0.0, 1.0],
        [0.0, 1.0, 1.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0, 0.0],
    ]

    # A normalized pair of Perron eigenvectors for the golden-mean adjacency
    # matrix; only the endpoint products are used below.
    right = [1.0 / sqrt(1.0 + a * a), a / sqrt(1.0 + a * a)]
    left = [right[0], right[1]]
    scale = sum(left[i] * right[i] for i in range(2))
    left = [x / scale for x in left]

    terminal_symbol = [0, 0, 1, 0, 0]
    posterior = [(1.0 + a * a) / 2.0, lam / 2.0, 0.5,
                 (1.0 + a * a) / 2.0, 0.5]
    ambiguity = [min(x, 1.0 - x) for x in posterior]
    initial = [1.0, 0.0, 0.0, 0.0, 0.0]
    s = [initial[i] * left[terminal_symbol[i]] for i in range(5)]
    t = [right[terminal_symbol[i]] * ambiguity[i] for i in range(5)]

    row = s
    for m in range(1, 9):
        matrix_value = sum(row[i] * t[i] for i in range(5)) / (lam ** (m - 1))
        k = m // 2
        closed_form = (1.0 / (2.0 * sqrt(5.0)) if k == 0 else
                       lam / 5.0 * lam ** (-k)
                       - 0.1 * (-lam ** (-3.0)) ** k)
        if abs(matrix_value - closed_form) > 1e-12:
            raise SystemExit(
                f"m={m}: matrix law {matrix_value} != closed form {closed_form}"
            )
        if m < 8:
            row = [sum(row[i] * B[i][j] for i in range(5))
                   for j in range(5)]


if __name__ == "__main__":
    main()
