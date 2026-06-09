#!/usr/bin/env python3
"""Legendre Picard-Fuchs and p-curvature certificate for T-43 / Q230.

Pure Python stdlib implementation: exact arithmetic uses fractions.Fraction.

The Picard-Fuchs operator is

    L = 4*l*(1-l) D^2 + 4*(1-2*l) D - 1.

Dividing by 4*l*(1-l) gives

    D^2 + p(l) D + q(l),  p=(1-2*l)/(l*(1-l)),
    q=-1/(4*l*(1-l)).

The companion connection for v=(period, D period) is v' = A v with

    A = [[0, 1], [-q, -p]]
      = [[0, 1], [1/(4*l*(1-l)), (2*l-1)/(l*(1-l))]].

Equivalently, with denominator l*(l-1), this is

    [[0, 1], [-1/(4*l*(l-1)), -(2*l-1)/(l*(l-1))]].

This derived companion convention is the one used below.  The prompt's displayed
matrix with denominator l*(l-1) and positive lower-row signs is not the
companion matrix of L under the stated convention.
"""

from __future__ import annotations

import json
import math
import os
import time
from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, Iterable, List, Optional, Sequence, Tuple


TARGET_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_JSON = os.path.join(TARGET_DIR, "legendre_p_curvature_output.json")
PRIMES = [5, 7, 11, 13, 17, 19, 23]


class Progress:
    def __init__(self, interval_seconds: float = 20.0) -> None:
        self.interval_seconds = interval_seconds
        self.last = 0.0

    def say(self, msg: str, force: bool = False) -> None:
        now = time.monotonic()
        if force or now - self.last >= self.interval_seconds:
            print(msg, flush=True)
            self.last = now


progress = Progress()


def _frac(value: int | Fraction) -> Fraction:
    if isinstance(value, Fraction):
        return value
    return Fraction(value, 1)


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
    def x() -> "Poly":
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
        ddeg = divisor.degree()
        dlc = divisor.lc()
        while len(rem) >= len(divisor.coeffs):
            coeff = rem[-1] / dlc
            shift = len(rem) - len(divisor.coeffs)
            quo[shift] = coeff
            for i, dc in enumerate(divisor.coeffs):
                rem[shift + i] -= coeff * dc
            while rem and rem[-1] == 0:
                rem.pop()
            if not rem:
                break
            if len(rem) - 1 < ddeg:
                break
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

    def pow(self, n: int) -> "Poly":
        if n < 0:
            raise ValueError("negative polynomial powers are not supported")
        result = Poly.one()
        base = self
        k = n
        while k:
            if k & 1:
                result = result * base
            base = base * base
            k >>= 1
        return result

    def eval_mod(self, value: int, p: int) -> int:
        acc = 0
        power = 1
        for c in self.coeffs:
            acc = (acc + fraction_mod(c, p) * power) % p
            power = (power * value) % p
        return acc

    def to_mod_coeffs(self, p: int) -> List[int]:
        out = [fraction_mod(c, p) for c in self.coeffs]
        while out and out[-1] == 0:
            out.pop()
        return out

    def __str__(self) -> str:
        if self.is_zero():
            return "0"
        parts = []
        for i, c in enumerate(self.coeffs):
            if c == 0:
                continue
            if i == 0:
                mon = ""
            elif i == 1:
                mon = "lambda"
            else:
                mon = f"lambda^{i}"
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
            raise ZeroDivisionError("rational function denominator is zero")
        if num.is_zero():
            object.__setattr__(self, "num", Poly.zero())
            object.__setattr__(self, "den", Poly.one())
            return
        g = num.gcd(den)
        qn, rn = num.divmod(g)
        qd, rd = den.divmod(g)
        if not rn.is_zero() or not rd.is_zero():
            raise ArithmeticError("internal polynomial gcd division failed")
        lc = qd.lc()
        qn = qn.scale(1 / lc)
        qd = qd.scale(1 / lc)
        object.__setattr__(self, "num", qn)
        object.__setattr__(self, "den", qd)

    @staticmethod
    def zero() -> "Rat":
        return Rat(0)

    @staticmethod
    def one() -> "Rat":
        return Rat(1)

    @staticmethod
    def x() -> "Rat":
        return Rat(Poly.x())

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

    def __truediv__(self, other: "Rat") -> "Rat":
        if other.is_zero():
            raise ZeroDivisionError("rational function division by zero")
        return Rat(self.num * other.den, self.den * other.num)

    def scale(self, scalar: int | Fraction) -> "Rat":
        return Rat(self.num.scale(scalar), self.den)

    def derivative(self) -> "Rat":
        return Rat(self.num.derivative() * self.den - self.num * self.den.derivative(), self.den * self.den)

    def to_mod(self, p: int) -> Dict[str, object]:
        num = poly_mod(self.num, p)
        den = poly_mod(self.den, p)
        if not den:
            return {
                "ok": False,
                "reason": f"denominator reduces to zero modulo {p}",
                "numerator": num,
                "denominator": den,
            }
        g = poly_gcd_mod(num, den, p)
        if len(g) > 1 or (g and g[0] != 1):
            num, _ = poly_divmod_mod(num, g, p)
            den, _ = poly_divmod_mod(den, g, p)
        if not den:
            den = [1]
        inv_lc = pow(den[-1], -1, p)
        num = [(c * inv_lc) % p for c in num]
        den = [(c * inv_lc) % p for c in den]
        num = trim_mod(num)
        den = trim_mod(den) or [1]
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
        num = poly_mod_to_str(data["numerator"], p)
        den_coeffs = data["denominator"]
        den = poly_mod_to_str(den_coeffs, p)
        if den_coeffs == [1]:
            return num
        return f"({num})/({den})"

    def __str__(self) -> str:
        if self.den == Poly.one():
            return str(self.num)
        return f"({self.num})/({self.den})"


def format_fraction(c: Fraction) -> str:
    if c.denominator == 1:
        return str(c.numerator)
    return f"{c.numerator}/{c.denominator}"


def fraction_mod(c: Fraction, p: int) -> int:
    num = c.numerator % p
    den = c.denominator % p
    if den == 0:
        raise ZeroDivisionError(f"coefficient denominator {c.denominator} is 0 mod {p}")
    return (num * pow(den, -1, p)) % p


def trim_mod(poly: Sequence[int]) -> List[int]:
    out = [int(c) for c in poly]
    while out and out[-1] == 0:
        out.pop()
    return out


def poly_mod(poly: Poly, p: int) -> List[int]:
    return trim_mod([fraction_mod(c, p) for c in poly.coeffs])


def poly_add_mod(a: Sequence[int], b: Sequence[int], p: int) -> List[int]:
    n = max(len(a), len(b))
    return trim_mod(
        [((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % p for i in range(n)]
    )


def poly_sub_mod(a: Sequence[int], b: Sequence[int], p: int) -> List[int]:
    n = max(len(a), len(b))
    return trim_mod(
        [((a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)) % p for i in range(n)]
    )


def poly_mul_mod(a: Sequence[int], b: Sequence[int], p: int) -> List[int]:
    if not a or not b:
        return []
    out = [0 for _ in range(len(a) + len(b) - 1)]
    for i, av in enumerate(a):
        for j, bv in enumerate(b):
            out[i + j] = (out[i + j] + av * bv) % p
    return trim_mod(out)


def poly_divmod_mod(a: Sequence[int], b: Sequence[int], p: int) -> Tuple[List[int], List[int]]:
    a = trim_mod(a)
    b = trim_mod(b)
    if not b:
        raise ZeroDivisionError("mod-p polynomial division by zero")
    if not a or len(a) < len(b):
        return [], a
    rem = list(a)
    quo = [0 for _ in range(len(a) - len(b) + 1)]
    inv_lc = pow(b[-1], -1, p)
    while rem and len(rem) >= len(b):
        coeff = rem[-1] * inv_lc % p
        shift = len(rem) - len(b)
        quo[shift] = coeff
        for i, bc in enumerate(b):
            rem[shift + i] = (rem[shift + i] - coeff * bc) % p
        rem = trim_mod(rem)
    return trim_mod(quo), rem


def poly_gcd_mod(a: Sequence[int], b: Sequence[int], p: int) -> List[int]:
    a = trim_mod(a)
    b = trim_mod(b)
    if not a:
        return make_monic_mod(b, p)
    if not b:
        return make_monic_mod(a, p)
    while b:
        _, r = poly_divmod_mod(a, b, p)
        a, b = b, r
    return make_monic_mod(a, p)


def make_monic_mod(a: Sequence[int], p: int) -> List[int]:
    a = trim_mod(a)
    if not a:
        return []
    inv = pow(a[-1], -1, p)
    return trim_mod([(c * inv) % p for c in a])


def denominator_roots_mod(den: Sequence[int], p: int) -> List[int]:
    if den == [1]:
        return []
    roots = []
    for x in range(p):
        acc = 0
        power = 1
        for c in den:
            acc = (acc + c * power) % p
            power = (power * x) % p
        if acc == 0:
            roots.append(x)
    return roots


def poly_mod_to_str(coeffs: Sequence[int], p: int) -> str:
    coeffs = trim_mod(coeffs)
    if not coeffs:
        return "0"
    parts = []
    for i, c in enumerate(coeffs):
        c %= p
        if c == 0:
            continue
        if i == 0:
            mon = ""
        elif i == 1:
            mon = "lambda"
        else:
            mon = f"lambda^{i}"
        if mon:
            if c == 1:
                parts.append(mon)
            else:
                parts.append(f"{c}*{mon}")
        else:
            parts.append(str(c))
    return " + ".join(parts) if parts else "0"


def binomial(n: int, k: int) -> int:
    return math.comb(n, k)


def rat_const(value: int | Fraction) -> Rat:
    return Rat(value)


def rat_poly(coeffs: Iterable[int | Fraction]) -> Rat:
    return Rat(Poly(coeffs))


def matrix_zero(n: int, m: int) -> List[List[Rat]]:
    return [[Rat.zero() for _ in range(m)] for _ in range(n)]


def matrix_add(a: List[List[Rat]], b: List[List[Rat]]) -> List[List[Rat]]:
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def matrix_mul(a: List[List[Rat]], b: List[List[Rat]]) -> List[List[Rat]]:
    n, mid, m = len(a), len(b), len(b[0])
    out = matrix_zero(n, m)
    for i in range(n):
        for j in range(m):
            s = Rat.zero()
            for k in range(mid):
                s = s + a[i][k] * b[k][j]
            out[i][j] = s
    return out


def matrix_derivative(a: List[List[Rat]]) -> List[List[Rat]]:
    return [[entry.derivative() for entry in row] for row in a]


def matrix_is_zero_mod_p(a: List[List[Rat]], p: int) -> bool:
    for row in a:
        for entry in row:
            data = entry.to_mod(p)
            if not data["ok"]:
                return False
            if data["numerator"]:
                return False
    return True


def matrix_str_mod_p(a: List[List[Rat]], p: int) -> str:
    rows = []
    for row in a:
        rows.append("[" + ", ".join(entry.str_mod(p) for entry in row) + "]")
    return "[" + ", ".join(rows) + "]"


def matrix_mod_data(a: List[List[Rat]], p: int) -> List[List[Dict[str, object]]]:
    return [[entry.to_mod(p) for entry in row] for row in a]


def matrix_det_2(a: List[List[Rat]]) -> Rat:
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def legendre_connection_A() -> List[List[Rat]]:
    lam = Poly.x()
    one_minus_lam = Poly((1, -1))
    den = lam * one_minus_lam
    return [
        [Rat.zero(), Rat.one()],
        [Rat(Poly((Fraction(1, 4),)), den), Rat(Poly((-1, 2)), den)],
    ]


def sym2_connection(A: List[List[Rat]]) -> List[List[Rat]]:
    a, b = A[0][0], A[0][1]
    c, d = A[1][0], A[1][1]
    return [
        [a.scale(2), b.scale(2), Rat.zero()],
        [c, a + d, b],
        [Rat.zero(), c.scale(2), d.scale(2)],
    ]


def p_curvature(A: List[List[Rat]], p: int) -> List[List[Rat]]:
    N = A
    for k in range(1, p):
        progress.say(f"  p={p}: recursion step {k + 1}/{p}")
        N = matrix_add(matrix_mul(N, A), matrix_derivative(N))
    return N


def phase_a_picard_fuchs() -> Dict[str, object]:
    progress.say("Phase A: verifying Picard-Fuchs equation on hypergeometric series.", force=True)
    coeffs = [Fraction(1)]
    for n in range(15):
        coeffs.append(coeffs[-1] * Fraction((2 * n + 1) ** 2, 4 * (n + 1) ** 2))

    # Coefficient of lambda^m in L(sum c_n lambda^n) is
    # 4*(m+1)^2*c_{m+1} - (2*m+1)^2*c_m.
    L_coeffs = []
    for m in range(15):
        L_coeffs.append(4 * (m + 1) ** 2 * coeffs[m + 1] - (2 * m + 1) ** 2 * coeffs[m])

    verified = all(c == 0 for c in L_coeffs)
    return {
        "verified": verified,
        "hypergeometric_coefficients_c0_through_c15": [format_fraction(c) for c in coeffs],
        "L_applied_coefficients_lambda0_through_lambda14": [format_fraction(c) for c in L_coeffs],
        "connection_convention": (
            "Using the companion matrix derived from L: "
            "A=[[0,1],[1/(4*lambda*(1-lambda)),(2*lambda-1)/(lambda*(1-lambda))]]. "
            "Equivalently lower row is negative over lambda*(lambda-1)."
        ),
    }


def phase_b_toy_check() -> Dict[str, object]:
    progress.say("Phase B: recording recursion and checking p=2 toy case.", force=True)
    x = Rat.x()
    A_toy = [[x]]
    N2 = p_curvature(A_toy, 2)[0][0]
    data = N2.to_mod(2)
    return {
        "description": (
            "For connection operator nabla_partial = partial - A, this certificate follows the "
            "requested iteration N_1=A and N_{k+1}=N_k*A + dN_k/dlambda; psi_p=N_p mod p. "
            "The sign convention is therefore the prompt's computational convention."
        ),
        "p_2_toy_case": {
            "A": "[[lambda]]",
            "N_2_over_Q": str(N2),
            "N_2_mod_2": Rat(N2.num, N2.den).str_mod(2),
            "expected": "lambda^2 + 1 in F_2[lambda]",
            "passes": data["ok"] and data["numerator"] == [1, 0, 1] and data["denominator"] == [1],
        },
    }


def hasse_polynomial_mod(p: int) -> List[int]:
    n = (p - 1) // 2
    return trim_mod([(binomial(n, i) ** 2) % p for i in range(n + 1)])


def divisibility_by_hasse(r: Rat, p: int, hasse: Sequence[int]) -> Dict[str, object]:
    data = r.to_mod(p)
    if not data["ok"]:
        return {
            "ok": False,
            "reason": data["reason"],
            "source": "bad reduction of rational function",
        }
    numerator = data["numerator"]
    if not numerator:
        return {
            "ok": True,
            "divides": True,
            "nonzero_witness": False,
            "source": "zero numerator",
            "quotient": "0",
            "remainder": "0",
        }
    _, rem = poly_divmod_mod(numerator, hasse, p)
    quotient, rem2 = poly_divmod_mod(numerator, hasse, p)
    return {
        "ok": True,
        "divides": not rem,
        "nonzero_witness": not rem and bool(numerator),
        "source": "determinant numerator in F_p(lambda)",
        "quotient": poly_mod_to_str(quotient, p),
        "remainder": poly_mod_to_str(rem2, p),
    }


def entries_divisible_by_hasse(matrix: List[List[Rat]], p: int, hasse: Sequence[int]) -> List[Dict[str, object]]:
    hits = []
    for i, row in enumerate(matrix):
        for j, entry in enumerate(row):
            data = entry.to_mod(p)
            if not data["ok"]:
                hits.append({"entry": [i, j], "ok": False, "reason": data["reason"]})
                continue
            numerator = data["numerator"]
            quotient, rem = poly_divmod_mod(numerator, hasse, p) if numerator else ([], [])
            hits.append(
                {
                    "entry": [i, j],
                    "ok": True,
                    "numerator": poly_mod_to_str(numerator, p),
                    "divisible_by_hasse": not rem,
                    "nonzero_witness": bool(numerator) and not rem,
                    "quotient": poly_mod_to_str(quotient, p),
                    "remainder": poly_mod_to_str(rem, p),
                }
            )
    return hits


def phase_c_p_curvatures(A: List[List[Rat]]) -> Tuple[Dict[str, object], bool]:
    progress.say("Phase C: computing p-curvature matrices for p=5,7,11,13,17,19,23.", force=True)
    results: Dict[str, object] = {}
    all_expected = True
    for p in PRIMES:
        progress.say(f"Phase C: starting p={p}.", force=True)
        try:
            psi = p_curvature(A, p)
            hasse = hasse_polynomial_mod(p)
            det = matrix_det_2(psi)
            is_zero = matrix_is_zero_mod_p(psi, p)
            det_div = divisibility_by_hasse(det, p, hasse)
            entry_divs = entries_divisible_by_hasse(psi, p, hasse)
            found_entry = any(item.get("ok") and item.get("nonzero_witness") for item in entry_divs)
            found_det = bool(det_div.get("ok") and det_div.get("nonzero_witness"))
            found = found_det or found_entry
            if is_zero or not found:
                all_expected = False
            singular = sorted(
                {
                    root
                    for row in matrix_mod_data(psi, p)
                    for entry in row
                    if entry.get("ok")
                    for root in entry.get("singular_residue_classes", [])
                }
            )
            results[str(p)] = {
                "psi_p_matrix": matrix_str_mod_p(psi, p),
                "psi_p_matrix_mod_data": matrix_mod_data(psi, p),
                "is_zero": is_zero,
                "hasse_polynomial": poly_mod_to_str(hasse, p),
                "hasse_coefficients_low_to_high": hasse,
                "det_psi_p": det.str_mod(p),
                "det_numerator_divisible_by_hasse": det_div,
                "entry_hasse_divisibility_scan": entry_divs,
                "hasse_detected_in_det_or_entry": found,
                "hasse_detection_basis": (
                    "nonzero determinant numerator" if found_det else
                    "nonzero p-curvature entry numerator" if found_entry else
                    "not detected"
                ),
                "singular_residue_classes_from_denominators": singular,
            }
            progress.say(
                f"Phase C: p={p} done; psi_p zero? {is_zero}; Hasse detected? {found}.",
                force=True,
            )
        except Exception as exc:
            all_expected = False
            results[str(p)] = {
                "error": repr(exc),
                "is_zero": None,
                "hasse_polynomial": poly_mod_to_str(hasse_polynomial_mod(p), p),
            }
            progress.say(f"Phase C: p={p} failed with {exc!r}.", force=True)
    return results, all_expected


def phase_d_sym2(A: List[List[Rat]], phase_c_results: Dict[str, object]) -> Tuple[Dict[str, object], bool]:
    progress.say("Phase D: building Sym^2 connection and recording Q230 vacuity check.", force=True)
    A2 = sym2_connection(A)
    all_nonzero = all(result.get("is_zero") is False for result in phase_c_results.values() if isinstance(result, dict))
    complete = len(phase_c_results) == len(PRIMES) and all_nonzero
    explanation = (
        "The Sym^2 connection on basis (eta_1^2, eta_1 eta_2, eta_2^2) is built from "
        "A=[[a,b],[c,d]] as [[2a,2b,0],[c,a+d,b],[0,2c,2d]]. "
        "A projector whose image is a one-dimensional cycle-class line C has zero induced "
        "codomain class in Sym^2H/C by definition, but the Q230 direct-proof hypothesis "
        "requires the relevant image to have vanishing p-curvature for all good p. "
        "The computed Legendre p-curvature is nonzero for every tested p>=5, matching the "
        "Honda/Katz expectation for this non-isotrivial family. Thus Q230 is vacuously "
        "verified for the Legendre family because the hypothesis fails (psi_p != 0 for all "
        "tested p >= 5); no horizontal idempotent with psi_p(im e)=0 for all p is produced "
        "inside this family."
    )
    return (
        {
            "hypothesis_vacuous": complete,
            "A_sym2": [[str(entry) for entry in row] for row in A2],
            "A_sym2_formula": "For A=[[a,b],[c,d]], Sym^2(A)=[[2a,2b,0],[c,a+d,b],[0,2c,2d]].",
            "projector_to_cycle_line_quotient_comment": (
                "If e is an idempotent with image C and C is quotiented out, the induced "
                "class of e(v) in Sym^2H/C is zero. This tautology is not a proof of Q230; "
                "the decisive computational point here is failure of the vanishing "
                "p-curvature hypothesis."
            ),
            "explanation": explanation,
        },
        complete,
    )


def main() -> int:
    started = time.time()
    progress.say("Legendre p-curvature engine starting.", force=True)

    phase_a = phase_a_picard_fuchs()
    phase_b = phase_b_toy_check()
    A = legendre_connection_A()
    phase_c, phase_c_ok = phase_c_p_curvatures(A)
    phase_d, phase_d_ok = phase_d_sym2(A, phase_c)

    phase_a_ok = bool(phase_a["verified"])
    phase_b_ok = bool(phase_b["p_2_toy_case"]["passes"])
    closure_ok = phase_a_ok and phase_b_ok and phase_c_ok and phase_d_ok
    if closure_ok:
        closure_grade = "YES"
        closure_reason = "Phases A, B, C, and D completed with expected nonzero p-curvature and Hasse checks."
    else:
        closure_grade = "NO"
        closure_reason = (
            f"phase_a_ok={phase_a_ok}, phase_b_ok={phase_b_ok}, "
            f"phase_c_ok={phase_c_ok}, phase_d_ok={phase_d_ok}"
        )

    cert = {
        "phase_a_picard_fuchs_verified": phase_a_ok,
        "phase_a_details": phase_a,
        "phase_b_p_curvature_recursion": phase_b,
        "phase_c_results": phase_c,
        "phase_d_q230_sym_squared": phase_d,
        "phase_e_closure_grade": closure_grade,
        "phase_e_closure_grade_reason": closure_reason,
        "interpretation_for_litt_conjecture_2": (
            "This concrete Legendre Sym^2 computation supports Q230 only as a boundary/vacuity "
            "check for direct-proof option (2): in the non-isotrivial Legendre family the "
            "rank-2 Gauss-Manin p-curvature is already nonzero for the tested good primes, "
            "with the classical Hasse polynomial visible in the mod-p calculation. Therefore "
            "the option requiring a horizontal idempotent whose image has zero p-curvature does "
            "not get a nontrivial Legendre test case; the hypothesis fails before any quotient "
            "idempotent obstruction has to be resolved."
        ),
        "runtime_seconds": round(time.time() - started, 3),
    }

    with open(OUTPUT_JSON, "w", encoding="utf-8") as f:
        json.dump(cert, f, indent=2, sort_keys=True)
        f.write("\n")

    print(f"Wrote JSON certificate: {OUTPUT_JSON}", flush=True)
    print(f"Closure-grade verdict: {closure_grade} ({closure_reason})", flush=True)
    return 0 if closure_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
