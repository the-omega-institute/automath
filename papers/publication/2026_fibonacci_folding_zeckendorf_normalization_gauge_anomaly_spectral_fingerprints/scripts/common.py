from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Tuple

try:
    import sympy as sp
except ImportError as e:  # pragma: no cover
    raise SystemExit(
        "缺少依赖 sympy。请先安装：\n"
        "  python3 -m pip install sympy\n"
    ) from e


R = sp.Rational


def assert_equal(got, expected, msg: str) -> None:
    if got != expected:
        raise AssertionError(f"{msg}\n  got: {got}\n  expected: {expected}")


def assert_simplify_zero(expr, msg: str) -> None:
    simplified = sp.simplify(expr)
    if simplified != 0:
        raise AssertionError(f"{msg}\n  simplify(expr) = {simplified}\n  expr = {expr}")


@dataclass(frozen=True)
class ParryMeasure:
    A: sp.Matrix
    lam: sp.Expr
    r: sp.Matrix
    l: sp.Matrix
    P: sp.Matrix
    pi: sp.Matrix


def pair_sofic_adjacency() -> sp.Matrix:
    """
    4-state sofic adjacency used in Sec.4 (bulk (X,Y) process).
    State order is (0,1,2,3).
    """
    return sp.Matrix(
        [
            [1, 1, 0, 1],
            [0, 0, 1, 0],
            [1, 2, 0, 0],
            [1, 0, 0, 0],
        ]
    )


def compute_parry_measure(A: sp.Matrix) -> ParryMeasure:
    """
    Compute Parry (max-entropy) Markov chain on states of a primitive adjacency A.
    Returns Perron eigenvalue lam, right/left eigenvectors r,l normalized so l^T r = 1,
    transition matrix P, and stationary state distribution pi (sum=1).
    """
    eig = A.eigenvals()  # dict eigenvalue -> mult
    # Choose Perron eigenvalue by maximal real part, then maximal magnitude.
    candidates = list(eig.keys())
    lam = max(candidates, key=lambda v: (sp.re(v).evalf(), abs(complex(sp.N(v)))))

    # Right/left eigenvectors
    r_ns = (A - lam * sp.eye(A.rows)).nullspace()
    l_ns = (A.T - lam * sp.eye(A.rows)).nullspace()
    if not r_ns or not l_ns:  # pragma: no cover
        raise RuntimeError("未能找到 Perron 特征向量（nullspace 为空）。")
    r = r_ns[0]
    l = l_ns[0]

    # Normalize so that l^T r = 1
    lr = (l.T * r)[0]
    r = sp.simplify(r / lr)

    # Parry transition matrix
    P = sp.Matrix(A.rows, A.cols, lambda i, j: 0)
    for i in range(A.rows):
        for j in range(A.cols):
            if A[i, j] != 0:
                P[i, j] = sp.simplify(A[i, j] * r[j] / (lam * r[i]))

    # Stationary state distribution pi_i = l_i * r_i, normalized
    pi = sp.Matrix([sp.simplify(l[i] * r[i]) for i in range(A.rows)])
    pi = sp.simplify(pi / sum(pi))

    return ParryMeasure(A=A, lam=lam, r=r, l=l, P=P, pi=pi)


def fib_sequence(n: int) -> list[int]:
    """
    Fibonacci numbers F_0..F_n with F_0=0, F_1=1.
    """
    if n < 0:
        raise ValueError("n must be >= 0")
    if n == 0:
        return [0]
    F = [0, 1]
    for _ in range(2, n + 1):
        F.append(F[-1] + F[-2])
    return F


def zeckendorf_bits_lsb(N: int, max_k: int, F: list[int]) -> list[int]:
    """
    Return z_1..z_{max_k} (LSB-first) in Zeckendorf representation of N:
      N = sum_{k>=1} z_k F_{k+1}, with no adjacent 1s.
    Only the first max_k digits are returned (higher digits are ignored).
    """
    if N < 0:
        raise ValueError("N must be >= 0")
    z = [0] * (max_k + 1)  # 1..max_k
    if N == 0:
        return z[1:]

    # Find largest Fibonacci index j (>=2) with F[j] <= N.
    j = len(F) - 1
    while j >= 2 and F[j] > N:
        j -= 1

    # Greedy selection, skipping adjacent Fibonacci numbers.
    while N > 0 and j >= 2:
        if F[j] <= N:
            k = j - 1  # digit index
            if 1 <= k <= max_k:
                z[k] = 1
            N -= F[j]
            j -= 2
        else:
            j -= 1

    return z[1:]


def fold_bits_lsb(word_bits_lsb: Iterable[int], F: list[int]) -> list[int]:
    """
    Implement Fold_m on a finite word given in LSB-first index convention:
      word_bits_lsb = [omega_1, ..., omega_m] with weights F_{k+1}.
    Returns Zeckendorf digits z_1..z_m (LSB-first) truncated to length m.
    """
    bits = list(word_bits_lsb)
    m = len(bits)
    N = 0
    for k, bit in enumerate(bits, start=1):
        if bit:
            N += F[k + 1]
    return zeckendorf_bits_lsb(N, m, F)


def gauge_anomaly_Gm(m: int, omega_mplus1_lsb: Iterable[int], F: list[int]) -> int:
    """
    Compute G_m(omega) for omega in Omega_{m+1} given as LSB-first bits.
    Using the explicit formula:
      re_{m+1->m}(omega) = pi_{m+1->m}(Fold_{m+1}(omega)),
      naive truncation is omega[1..m].
    """
    omega = list(omega_mplus1_lsb)
    if len(omega) != m + 1:
        raise ValueError("omega length must be m+1")
    z = fold_bits_lsb(omega, F)  # Fold_{m+1}(omega), truncated to length m+1
    naive = omega[:m]
    aware = z[:m]
    return sum(a ^ b for a, b in zip(naive, aware))


def omega_star(m: int) -> list[int]:
    """
    Explicit worst-case family omega^* of length m+1 used in Remark 4.??:
      Let L=m+1=3n+r, r in {0,1,2}.
        r=0: (110)^n
        r=1: (110)^n 0
        r=2: (110)^n 11
    Returned as LSB-first bits [omega_1,...,omega_{m+1}].
    """
    if m < 1:
        raise ValueError("m must be >= 1")
    L = m + 1
    n, r = divmod(L, 3)
    out: list[int] = []
    out += [1, 1, 0] * n
    if r == 0:
        pass
    elif r == 1:
        out += [0]
    elif r == 2:
        out += [1, 1]
    else:  # pragma: no cover
        raise RuntimeError("unreachable")
    if len(out) != L:  # pragma: no cover
        raise RuntimeError("omega_star length mismatch")
    return out

