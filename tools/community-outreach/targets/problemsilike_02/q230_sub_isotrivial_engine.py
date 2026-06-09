#!/usr/bin/env python3
"""Sub-isotrivial Gauss-Manin / p-curvature engine for T-43 / Litt #2 / Q230.

This is a pure-stdlib arithmetic checker.  It intentionally uses exact
fractions over Q and explicit mod-p rational-function reduction; no sympy,
numpy, sage, or external CAS is used.

The main family is the smooth proper abelian-surface family

    X_t = E_t x E_CM over B = Spec Q[t, 1/(t(t-1))]

where E_t is the Legendre curve y^2 = x(x-1)(x-t), and E_CM is the fixed
CM elliptic curve y^2 = x^3 - x.  On H^1_dR the Gauss-Manin connection is a
direct sum: the displayed Legendre connection in the basis
(dx/y, x dx/y), and a zero connection on the fixed CM factor.

The target point is not to prove a theorem about Q230.  It is to produce a
closure-grade concrete family where the p-curvature hypothesis is non-vacuous:
the fixed factor has zero p-curvature, while the full H still contains a
nonzero Legendre p-curvature block.
"""

from __future__ import annotations

import json
import os
import time
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple


TARGET = "T-43 / Litt #2 / Q230"
PRIMES = [5, 7, 11, 13]
ROOT = Path(__file__).resolve().parent
OUTPUT_JSON = ROOT / "q230_sub_isotrivial_engine_output.json"


class Progress:
    def __init__(self, interval_seconds: float = 20.0) -> None:
        self.interval_seconds = interval_seconds
        self.last = 0.0

    def say(self, message: str, force: bool = False) -> None:
        now = time.monotonic()
        if force or now - self.last >= self.interval_seconds:
            print(message, flush=True)
            self.last = now


progress = Progress()


def _frac(value: int | Fraction) -> Fraction:
    return value if isinstance(value, Fraction) else Fraction(value, 1)


@dataclass(frozen=True)
class Poly:
    coeffs: Tuple[Fraction, ...]

    def __init__(self, coeffs: Iterable[int | Fraction] = ()) -> None:
        cs = tuple(_frac(c) for c in coeffs)
        end = len(cs)
        while end > 0 and cs[end - 1] == 0:
            end -= 1
        object.__setattr__(self, "coeffs", cs[:end])

    @staticmethod
    def zero() -> "Poly":
        return Poly(())

    @staticmethod
    def one() -> "Poly":
        return Poly((1,))

    @staticmethod
    def t() -> "Poly":
        return Poly((0, 1))

    def is_zero(self) -> bool:
        return not self.coeffs

    def degree(self) -> int:
        return len(self.coeffs) - 1

    def lc(self) -> Fraction:
        if self.is_zero():
            return Fraction(0)
        return self.coeffs[-1]

    def __add__(self, other: "Poly") -> "Poly":
        n = max(len(self.coeffs), len(other.coeffs))
        return Poly(
            (self.coeffs[i] if i < len(self.coeffs) else 0)
            + (other.coeffs[i] if i < len(other.coeffs) else 0)
            for i in range(n)
        )

    def __neg__(self) -> "Poly":
        return Poly(-c for c in self.coeffs)

    def __sub__(self, other: "Poly") -> "Poly":
        return self + (-other)

    def __mul__(self, other: "Poly") -> "Poly":
        if self.is_zero() or other.is_zero():
            return Poly.zero()
        out = [Fraction(0) for _ in range(len(self.coeffs) + len(other.coeffs) - 1)]
        for i, a in enumerate(self.coeffs):
            for j, b in enumerate(other.coeffs):
                out[i + j] += a * b
        return Poly(out)

    def scale(self, scalar: int | Fraction) -> "Poly":
        s = _frac(scalar)
        if s == 0 or self.is_zero():
            return Poly.zero()
        return Poly(c * s for c in self.coeffs)

    def derivative(self) -> "Poly":
        if len(self.coeffs) <= 1:
            return Poly.zero()
        return Poly(self.coeffs[i] * i for i in range(1, len(self.coeffs)))

    def divmod(self, divisor: "Poly") -> Tuple["Poly", "Poly"]:
        if divisor.is_zero():
            raise ZeroDivisionError("polynomial division by zero")
        if self.is_zero() or self.degree() < divisor.degree():
            return Poly.zero(), self
        rem = list(self.coeffs)
        quo = [Fraction(0) for _ in range(self.degree() - divisor.degree() + 1)]
        dlc = divisor.lc()
        while rem and len(rem) >= len(divisor.coeffs):
            coeff = rem[-1] / dlc
            shift = len(rem) - len(divisor.coeffs)
            quo[shift] = coeff
            for i, dc in enumerate(divisor.coeffs):
                rem[shift + i] -= coeff * dc
            while rem and rem[-1] == 0:
                rem.pop()
        return Poly(quo), Poly(rem)

    def monic(self) -> "Poly":
        if self.is_zero():
            return self
        return self.scale(1 / self.lc())

    def gcd(self, other: "Poly") -> "Poly":
        a, b = self, other
        if a.is_zero():
            return b.monic()
        if b.is_zero():
            return a.monic()
        while not b.is_zero():
            _, r = a.divmod(b)
            a, b = b, r
        return a.monic()

    def __str__(self) -> str:
        if self.is_zero():
            return "0"
        parts: List[str] = []
        for i, c in enumerate(self.coeffs):
            if c == 0:
                continue
            if i == 0:
                mon = ""
            elif i == 1:
                mon = "t"
            else:
                mon = f"t^{i}"
            if mon:
                if c == 1:
                    parts.append(mon)
                elif c == -1:
                    parts.append(f"-{mon}")
                else:
                    parts.append(f"{format_fraction(c)}*{mon}")
            else:
                parts.append(format_fraction(c))
        return " + ".join(parts).replace("+ -", "- ")


@dataclass(frozen=True)
class Rat:
    num: Poly
    den: Poly

    def __init__(self, num: Poly | int | Fraction = 0, den: Poly | int | Fraction = 1) -> None:
        if not isinstance(num, Poly):
            num = Poly((num,))
        if not isinstance(den, Poly):
            den = Poly((den,))
        if den.is_zero():
            raise ZeroDivisionError("rational-function denominator is zero")
        if num.is_zero():
            object.__setattr__(self, "num", Poly.zero())
            object.__setattr__(self, "den", Poly.one())
            return
        g = num.gcd(den)
        qn, rn = num.divmod(g)
        qd, rd = den.divmod(g)
        if not rn.is_zero() or not rd.is_zero():
            raise ArithmeticError("internal gcd division failed")
        lc = qd.lc()
        object.__setattr__(self, "num", qn.scale(1 / lc))
        object.__setattr__(self, "den", qd.scale(1 / lc))

    @staticmethod
    def zero() -> "Rat":
        return Rat(0)

    @staticmethod
    def one() -> "Rat":
        return Rat(1)

    def is_zero(self) -> bool:
        return self.num.is_zero()

    def __add__(self, other: "Rat") -> "Rat":
        return Rat(self.num * other.den + other.num * self.den, self.den * other.den)

    def __neg__(self) -> "Rat":
        return Rat(-self.num, self.den)

    def __sub__(self, other: "Rat") -> "Rat":
        return self + (-other)

    def __mul__(self, other: "Rat") -> "Rat":
        return Rat(self.num * other.num, self.den * other.den)

    def derivative(self) -> "Rat":
        return Rat(self.num.derivative() * self.den - self.num * self.den.derivative(), self.den * self.den)

    def scale(self, scalar: int | Fraction) -> "Rat":
        return Rat(self.num.scale(scalar), self.den)

    def to_mod(self, p: int) -> dict[str, object]:
        num = poly_mod(self.num, p)
        den = poly_mod(self.den, p)
        if not den:
            return {"ok": False, "reason": f"denominator is zero modulo {p}", "numerator": num, "denominator": den}
        g = poly_gcd_mod(num, den, p)
        if len(g) > 1 or (g and g[0] != 1):
            num, _ = poly_divmod_mod(num, g, p)
            den, _ = poly_divmod_mod(den, g, p)
        inv_lc = pow(den[-1], -1, p)
        num = trim_mod([(c * inv_lc) % p for c in num])
        den = trim_mod([(c * inv_lc) % p for c in den]) or [1]
        return {
            "ok": True,
            "numerator": num,
            "denominator": den,
            "singular_residue_classes": denominator_roots_mod(den, p),
        }

    def str_mod(self, p: int) -> str:
        data = self.to_mod(p)
        if not data["ok"]:
            return f"<bad reduction: {data['reason']}>"
        numerator = poly_mod_to_str(data["numerator"], p)
        denominator = data["denominator"]
        if denominator == [1]:
            return numerator
        return f"({numerator})/({poly_mod_to_str(denominator, p)})"

    def __str__(self) -> str:
        if self.den == Poly.one():
            return str(self.num)
        return f"({self.num})/({self.den})"


def format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def fraction_mod(value: Fraction, p: int) -> int:
    denominator = value.denominator % p
    if denominator == 0:
        raise ZeroDivisionError(f"coefficient denominator {value.denominator} is 0 modulo {p}")
    return (value.numerator % p) * pow(denominator, -1, p) % p


def trim_mod(poly: Sequence[int]) -> List[int]:
    out = [int(c) for c in poly]
    while out and out[-1] == 0:
        out.pop()
    return out


def poly_mod(poly: Poly, p: int) -> List[int]:
    return trim_mod([fraction_mod(c, p) for c in poly.coeffs])


def poly_divmod_mod(a: Sequence[int], b: Sequence[int], p: int) -> Tuple[List[int], List[int]]:
    rem = trim_mod(a)
    divisor = trim_mod(b)
    if not divisor:
        raise ZeroDivisionError("mod-p polynomial division by zero")
    if not rem or len(rem) < len(divisor):
        return [], rem
    quotient = [0 for _ in range(len(rem) - len(divisor) + 1)]
    inv_lc = pow(divisor[-1], -1, p)
    while rem and len(rem) >= len(divisor):
        coeff = rem[-1] * inv_lc % p
        shift = len(rem) - len(divisor)
        quotient[shift] = coeff
        for i, dc in enumerate(divisor):
            rem[shift + i] = (rem[shift + i] - coeff * dc) % p
        rem = trim_mod(rem)
    return trim_mod(quotient), rem


def poly_gcd_mod(a: Sequence[int], b: Sequence[int], p: int) -> List[int]:
    x = trim_mod(a)
    y = trim_mod(b)
    if not x:
        return make_monic_mod(y, p)
    if not y:
        return make_monic_mod(x, p)
    while y:
        _, r = poly_divmod_mod(x, y, p)
        x, y = y, r
    return make_monic_mod(x, p)


def make_monic_mod(a: Sequence[int], p: int) -> List[int]:
    out = trim_mod(a)
    if not out:
        return []
    inv = pow(out[-1], -1, p)
    return trim_mod([(c * inv) % p for c in out])


def denominator_roots_mod(den: Sequence[int], p: int) -> List[int]:
    if den == [1]:
        return []
    roots: List[int] = []
    for value in range(p):
        acc = 0
        power = 1
        for coeff in den:
            acc = (acc + coeff * power) % p
            power = (power * value) % p
        if acc == 0:
            roots.append(value)
    return roots


def poly_mod_to_str(coeffs: Sequence[int], p: int) -> str:
    coeffs = trim_mod(coeffs)
    if not coeffs:
        return "0"
    parts: List[str] = []
    for i, c in enumerate(coeffs):
        c %= p
        if c == 0:
            continue
        if i == 0:
            mon = ""
        elif i == 1:
            mon = "t"
        else:
            mon = f"t^{i}"
        if mon:
            parts.append(mon if c == 1 else f"{c}*{mon}")
        else:
            parts.append(str(c))
    return " + ".join(parts) if parts else "0"


MatrixRat = List[List[Rat]]
MatrixQ = List[List[Fraction]]
VectorQ = List[Fraction]


def zero_matrix(rows: int, cols: int) -> MatrixRat:
    return [[Rat.zero() for _ in range(cols)] for _ in range(rows)]


def matrix_add(a: MatrixRat, b: MatrixRat) -> MatrixRat:
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def matrix_mul(a: MatrixRat, b: MatrixRat) -> MatrixRat:
    n, middle, m = len(a), len(b), len(b[0])
    out = zero_matrix(n, m)
    for i in range(n):
        for j in range(m):
            value = Rat.zero()
            for k in range(middle):
                value = value + a[i][k] * b[k][j]
            out[i][j] = value
    return out


def matrix_derivative(a: MatrixRat) -> MatrixRat:
    return [[entry.derivative() for entry in row] for row in a]


def matrix_is_zero_mod_p(a: MatrixRat, p: int) -> bool:
    return all(entry.to_mod(p).get("ok") is True and not entry.to_mod(p)["numerator"] for row in a for entry in row)


def p_curvature(connection: MatrixRat, p: int) -> MatrixRat:
    """Return N_p for d/dt + A using N_1=A, N_{k+1}=N_k A + dN_k/dt."""
    n = connection
    for step in range(1, p):
        progress.say(f"  p={p}: p-curvature recursion step {step + 1}/{p}")
        n = matrix_add(matrix_mul(n, connection), matrix_derivative(n))
    return n


def matrix_str(a: MatrixRat) -> List[List[str]]:
    return [[str(entry) for entry in row] for row in a]


def matrix_str_mod_p(a: MatrixRat, p: int) -> str:
    return "[" + ", ".join("[" + ", ".join(entry.str_mod(p) for entry in row) + "]" for row in a) + "]"


def restrict_matrix(a: MatrixRat, indices: Sequence[int]) -> MatrixRat:
    return [[a[i][j] for j in indices] for i in indices]


def block_diag(blocks: Sequence[MatrixRat]) -> MatrixRat:
    total = sum(len(block) for block in blocks)
    out = zero_matrix(total, total)
    offset = 0
    for block in blocks:
        for i, row in enumerate(block):
            for j, entry in enumerate(row):
                out[offset + i][offset + j] = entry
        offset += len(block)
    return out


def legendre_connection_prompt_basis() -> MatrixRat:
    """Gauss-Manin matrix for y^2=x(x-1)(x-t) in (dx/y, x dx/y).

    This is the matrix supplied in the task prompt:

        [[0, 1/(t(t-1))],
         [-1/(4 t(t-1)), -(2t-1)/(2 t(t-1))]].
    """
    t = Poly.t()
    den = t * Poly((-1, 1))  # t*(t-1)
    return [
        [Rat.zero(), Rat(Poly.one(), den)],
        [Rat(Poly((Fraction(-1, 4),)), den), Rat(Poly((Fraction(1, 2), -1)), den)],
    ]


def zero_connection(rank: int) -> MatrixRat:
    return zero_matrix(rank, rank)


def identity_q(rank: int) -> MatrixQ:
    return [[Fraction(1 if i == j else 0) for j in range(rank)] for i in range(rank)]


def diag_q(entries: Sequence[int]) -> MatrixQ:
    return [[Fraction(entries[i] if i == j else 0) for j in range(len(entries))] for i in range(len(entries))]


def mat_q_vec_mul(matrix: MatrixQ, vector: VectorQ) -> VectorQ:
    return [sum(matrix[i][j] * vector[j] for j in range(len(vector))) for i in range(len(matrix))]


def solve_square_q(matrix: MatrixQ, rhs: VectorQ) -> VectorQ:
    n = len(matrix)
    aug = [list(row) + [rhs[i]] for i, row in enumerate(matrix)]
    pivot_row = 0
    for col in range(n):
        pivot = None
        for row in range(pivot_row, n):
            if aug[row][col] != 0:
                pivot = row
                break
        if pivot is None:
            continue
        aug[pivot_row], aug[pivot] = aug[pivot], aug[pivot_row]
        inv = 1 / aug[pivot_row][col]
        aug[pivot_row] = [value * inv for value in aug[pivot_row]]
        for row in range(n):
            if row != pivot_row and aug[row][col] != 0:
                factor = aug[row][col]
                aug[row] = [aug[row][j] - factor * aug[pivot_row][j] for j in range(n + 1)]
        pivot_row += 1
    if pivot_row != n:
        raise ValueError("basis matrix is singular")
    return [aug[i][-1] for i in range(n)]


def columns_to_matrix(columns: Sequence[VectorQ]) -> MatrixQ:
    if not columns:
        return []
    rows = len(columns[0])
    return [[columns[j][i] for j in range(len(columns))] for i in range(rows)]


def induced_quotient_matrix(e: MatrixQ, c_basis: Sequence[VectorQ], quotient_reps: Sequence[VectorQ]) -> MatrixQ:
    """Compute the matrix induced by e on H/C in the chosen quotient representatives."""
    full_basis = list(c_basis) + list(quotient_reps)
    basis_matrix = columns_to_matrix(full_basis)
    qdim = len(quotient_reps)
    out = [[Fraction(0) for _ in range(qdim)] for _ in range(qdim)]
    for col, representative in enumerate(quotient_reps):
        image = mat_q_vec_mul(e, representative)
        coords = solve_square_q(basis_matrix, image)
        quotient_coords = coords[len(c_basis) :]
        for row, value in enumerate(quotient_coords):
            out[row][col] = value
    return out


def q_matrix_to_json(matrix: MatrixQ) -> List[List[str]]:
    return [[format_fraction(value) for value in row] for row in matrix]


def q_matrix_is_zero(matrix: MatrixQ) -> bool:
    return all(value == 0 for row in matrix for value in row)


def std_basis(rank: int, index: int) -> VectorQ:
    return [Fraction(1 if i == index else 0) for i in range(rank)]


def p_curvature_summary(connection: MatrixRat, primes: Sequence[int]) -> dict[str, str]:
    out: dict[str, str] = {}
    for p in primes:
        progress.say(f"Computing p-curvature for rank {len(connection)} connection at p={p}.", force=True)
        psi = p_curvature(connection, p)
        out[str(p)] = matrix_str_mod_p(psi, p)
    return out


def p_curvature_summary_with_restriction(
    connection: MatrixRat, primes: Sequence[int], indices: Sequence[int]
) -> tuple[dict[str, str], dict[str, str]]:
    full: dict[str, str] = {}
    restricted: dict[str, str] = {}
    for p in primes:
        progress.say(f"Computing p-curvature for rank {len(connection)} connection at p={p}.", force=True)
        psi = p_curvature(connection, p)
        full[str(p)] = matrix_str_mod_p(psi, p)
        restricted[str(p)] = matrix_str_mod_p(restrict_matrix(psi, indices), p)
    return full, restricted


def source_hypothesis_note() -> dict[str, object]:
    searched = []
    hits = []
    for name in ["lam_litt_2501.13175v1.txt", "litt_2409.02234v1.txt"]:
        path = ROOT / name
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        searched.append(name)
        for needle in ["Q230", "Question 230", "strict-zero quotient"]:
            if needle in text:
                hits.append({"file": name, "needle": needle})
    return {
        "searched_local_source_extracts": searched,
        "literal_hits": hits,
        "interpretation": (
            "The local source extracts did not expose a literal theorem-numbered Q230 statement "
            "during this engine run.  Existing local O231/O236/O247 audits record Q230 as the "
            "strict-zero p-curvature => quotient-idempotent-vanishing interface and state that "
            "available Lam-Litt/Litt anchors do not prove it for arbitrary summands."
        ),
    }


def build_legendre_cm_product_family() -> dict[str, object]:
    progress.say("Phase A/B: Legendre x fixed CM elliptic product.", force=True)
    legendre = legendre_connection_prompt_basis()
    cm = zero_connection(2)
    connection = block_diag([legendre, cm])
    full_psi, w_psi = p_curvature_summary_with_restriction(connection, PRIMES, [2, 3])

    e = diag_q([0, 0, 1, 1])
    c_hodge = [std_basis(4, 0), std_basis(4, 2)]  # omega_L, omega_CM
    quotient_hodge = [std_basis(4, 1), std_basis(4, 3)]  # eta_L, eta_CM
    q_hodge = induced_quotient_matrix(e, c_hodge, quotient_hodge)

    c_legendre = [std_basis(4, 0), std_basis(4, 1)]
    quotient_legendre = [std_basis(4, 2), std_basis(4, 3)]
    q_legendre = induced_quotient_matrix(e, c_legendre, quotient_legendre)

    return {
        "name": "Legendre elliptic curve times fixed CM elliptic curve",
        "base": "B = Spec Q[t, 1/(t(t-1))]",
        "fiber": (
            "X_t = E_t x E_CM with E_t: y^2 = x(x-1)(x-t), "
            "E_CM: y^2 = x^3 - x"
        ),
        "H_rank": 4,
        "basis": ["omega_L=dx/y", "eta_L=x dx/y", "omega_CM=dx/y", "eta_CM=x dx/y"],
        "GM_connection_full": matrix_str(connection),
        "GM_connection_derivation": (
            "Direct sum of the Picard-Fuchs/Gauss-Manin matrix for the explicit "
            "Legendre equation in basis (dx/y, x dx/y) and the zero connection "
            "for the fixed elliptic curve E_CM."
        ),
        "psi_p_full_H": full_psi,
        "sub_summand_W": {
            "description": "constant fixed-CM factor H^1_dR(E_CM)",
            "basis": ["omega_CM", "eta_CM"],
            "rank": 2,
            "projection": "e_s = projection H^1(E_t) direct-sum H^1(E_CM) -> H^1(E_CM)",
        },
        "psi_p_on_W": w_psi,
        "flag_C": {
            "description": "Hodge filtration F^1 H^1_dR(X_t) = <omega_L, omega_CM>",
            "basis": ["omega_L", "omega_CM"],
        },
        "e_s_matrix": q_matrix_to_json(e),
        "e_s_quotient_basis": ["eta_L mod F^1", "eta_CM mod F^1"],
        "e_s_quotient_matrix": q_matrix_to_json(q_hodge),
        "is_zero_on_quotient": q_matrix_is_zero(q_hodge),
        "alternative_flag_check": {
            "flag_C": {
                "description": "Legendre summand H^1_dR(E_t), the arbitrary flag suggested in the prompt",
                "basis": ["omega_L", "eta_L"],
            },
            "quotient_basis": ["omega_CM mod C", "eta_CM mod C"],
            "e_s_quotient_matrix": q_matrix_to_json(q_legendre),
            "is_zero_on_quotient": q_matrix_is_zero(q_legendre),
        },
        "q230_verdict": "counterexample",
        "verdict_explanation": (
            "The p-curvature on im(e_s)=H^1(E_CM) is zero for all p because the CM factor is fixed, "
            "but with C=F^1 the induced quotient map is diag(0,1), not zero.  Thus Q230 as a literal "
            "arbitrary smooth-proper Gauss-Manin summand statement needs an extra exclusion, such as "
            "ruling out constant direct factors or requiring a stronger cycle-span/quotient hypothesis."
        ),
    }


def build_constant_cm_family() -> dict[str, object]:
    progress.say("Phase A/B: constant CM elliptic family obstruction.", force=True)
    connection = zero_connection(2)
    full_psi, w_psi = p_curvature_summary_with_restriction(connection, PRIMES, [0, 1])

    e = identity_q(2)
    c_hodge = [std_basis(2, 0)]  # omega
    quotient = [std_basis(2, 1)]  # eta
    q = induced_quotient_matrix(e, c_hodge, quotient)

    return {
        "name": "constant CM elliptic curve with identity projector",
        "base": "B = Spec Q[t] (or the same open Spec Q[t,1/(t(t-1))])",
        "fiber": "X_t = E_CM: y^2 = x^3 - x, independent of t",
        "H_rank": 2,
        "basis": ["omega=dx/y", "eta=x dx/y"],
        "GM_connection_full": matrix_str(connection),
        "GM_connection_derivation": "The family is the pullback of a fixed smooth proper curve, so the relative H^1_dR bundle is constant and the Gauss-Manin matrix is zero.",
        "psi_p_full_H": full_psi,
        "sub_summand_W": {
            "description": "all of H^1_dR(E_CM), selected by the identity projector",
            "basis": ["omega", "eta"],
            "rank": 2,
            "projection": "e_s = id in the constant basis (omega, eta)",
        },
        "psi_p_on_W": w_psi,
        "flag_C": {
            "description": "Hodge filtration F^1 H^1_dR(E_CM) = <omega>",
            "basis": ["omega"],
        },
        "e_s_matrix": q_matrix_to_json(e),
        "e_s_quotient_basis": ["eta mod F^1"],
        "e_s_quotient_matrix": q_matrix_to_json(q),
        "is_zero_on_quotient": q_matrix_is_zero(q),
        "q230_verdict": "counterexample",
        "verdict_explanation": (
            "This is the trivial obstruction: all p-curvatures vanish because the whole family is constant, "
            "yet the induced idempotent on H/F^1 is the identity.  This family must be excluded by any "
            "non-isotriviality, geometric-correspondence, or stronger flag/cycle hypothesis intended in Q230."
        ),
    }


def build_payload() -> dict[str, object]:
    source_note = source_hypothesis_note()
    families = [build_legendre_cm_product_family(), build_constant_cm_family()]
    product = families[0]
    constant = families[1]
    return {
        "target": TARGET,
        "context": "sub-isotrivial family search",
        "previous_result": "Legendre vacuous (commit 9cdc5b197)",
        "primes_tested": PRIMES,
        "p_curvature_recursion": "N_1=A, N_{k+1}=N_k*A + dN_k/dt, psi_p=N_p mod p",
        "q230_hypothesis_audit": source_note,
        "families_investigated": families,
        "structural_finding": (
            "A sub-isotrivial fixed factor makes Q230's p-curvature premise genuinely non-vacuous: "
            "for X_t=E_t x E_CM, psi_p is nonzero on full H because of the Legendre block but zero on "
            "the proper direct summand W=H^1(E_CM).  Nevertheless, the projector onto W acts nontrivially "
            f"on H/F^1 with quotient matrix {product['e_s_quotient_matrix']}.  The fully constant family "
            f"shows the same obstruction in minimal rank with quotient matrix {constant['e_s_quotient_matrix']}. "
            "Therefore Q230 as literally phrased is not supported by these computations; it needs a hypothesis "
            "excluding constant/isotrivial direct factors or an additional cycle-span/quotient condition stronger "
            "than merely requiring a horizontal idempotent preserving F^1."
        ),
    }


def main() -> None:
    progress.say("Q230 sub-isotrivial engine starting.", force=True)
    payload = build_payload()
    OUTPUT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    progress.say(f"Wrote {OUTPUT_JSON}", force=True)


if __name__ == "__main__":
    main()
