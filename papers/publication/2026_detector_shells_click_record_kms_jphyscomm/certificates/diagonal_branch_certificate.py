from __future__ import annotations

import json
import sys
import unittest
from decimal import Decimal, getcontext, localcontext, ROUND_FLOOR, ROUND_CEILING
from pathlib import Path

STALE_TRACE_INTERVAL = (
    Decimal("68.4603940231"),
    Decimal("68.4603940232"),
)
STALE_DETERMINANT_INTERVAL = (
    Decimal("1.38769443609"),
    Decimal("1.38769443610"),
)
EXPECTED_ROUNDED = {
    "sigma": [
        ["25.0645227916081", "17.2222593244352"],
        ["17.2222593244352", "11.8884649865292"],
    ],
    "trace": "36.9529877781373",
    "det": "1.37248537400032",
}
TRANSCRIPT_PATH = Path(__file__).with_name("diagonal_branch_z_half.json")


def D(x: str) -> Decimal:
    return Decimal(x)


class Interval:
    def __init__(self, lo, hi=None):
        self.lo = Decimal(lo)
        self.hi = Decimal(lo if hi is None else hi)
        if self.lo > self.hi:
            raise ValueError((self.lo, self.hi))

    def __add__(self, other):
        other = I(other)
        return outward(lambda: self.lo + other.lo, lambda: self.hi + other.hi)

    def __sub__(self, other):
        other = I(other)
        return outward(lambda: self.lo - other.hi, lambda: self.hi - other.lo)

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __mul__(self, other):
        other = I(other)
        pairs = [
            (self.lo, other.lo),
            (self.lo, other.hi),
            (self.hi, other.lo),
            (self.hi, other.hi),
        ]
        with localcontext() as ctx:
            ctx.rounding = ROUND_FLOOR
            lows = [+(a * b) for a, b in pairs]
        with localcontext() as ctx:
            ctx.rounding = ROUND_CEILING
            highs = [+(a * b) for a, b in pairs]
        return Interval(min(lows), max(highs))

    def inv(self):
        if self.lo <= 0 <= self.hi:
            raise ZeroDivisionError(self)
        return outward(lambda: Decimal(1) / self.hi, lambda: Decimal(1) / self.lo)

    def __truediv__(self, other):
        return self * I(other).inv()

    def sq(self):
        if self.lo <= 0 <= self.hi:
            return outward(lambda: Decimal(0), lambda: max(self.lo * self.lo, self.hi * self.hi))
        return self * self

    def to_json(self):
        return [str(self.lo), str(self.hi)]

    def __repr__(self):
        return f"[{self.lo}, {self.hi}]"


def I(x) -> Interval:
    if isinstance(x, Interval):
        return x
    return Interval(x)


def outward(lo_fn, hi_fn) -> Interval:
    with localcontext() as ctx:
        ctx.rounding = ROUND_FLOOR
        lo = +lo_fn()
    with localcontext() as ctx:
        ctx.rounding = ROUND_CEILING
        hi = +hi_fn()
    return Interval(lo, hi)


def matmul(A, B):
    n = len(A)
    m = len(B[0])
    p = len(B)
    return [[sum_i([A[i][k] * B[k][j] for k in range(p)]) for j in range(m)] for i in range(n)]


def transpose(A):
    return [list(row) for row in zip(*A)]


def sum_i(xs):
    s = Interval(0)
    for x in xs:
        s = s + x
    return s


def add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def scalar_mul(c, A):
    return [[I(c) * A[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def outer(a, b):
    return [[a[i] * b[j] for j in range(len(b))] for i in range(len(a))]


def point_matmul(A, B):
    n = len(A)
    m = len(B[0])
    p = len(B)
    return [[sum(A[i][k] * B[k][j] for k in range(p)) for j in range(m)] for i in range(n)]


def point_transpose(A):
    return [list(row) for row in zip(*A)]


def point_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def point_sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def point_scalar_mul(c, A):
    return [[c * A[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def point_outer(a, b):
    return [[a[i] * b[j] for j in range(len(b))] for i in range(len(a))]


def printed_formula_point_values(prec: int = 90):
    with localcontext() as ctx:
        ctx.prec = prec
        z = Decimal(1) / Decimal(2)
        theta = Decimal(
            "0.69314718055994530941723212145817656807550013436025525412068000949339362196969471"
        )
        one = Decimal(1)
        omz = one - z
        g0 = omz - theta * z
        g1 = z * (omz * (one + theta) - theta * z)
        mu = one / omz + theta * z / (omz * omz)
        nu = (one + z) / (omz * omz) + theta * z * (Decimal(3) + z) / (omz * omz * omz)
        m2 = g1 + g0 * g0
        r = [one / mu, g0 / mu, m2 / mu]
        A = [
            [one, g0, m2],
            [g0, g0, g0 * g0],
            [m2, g0 * g0, m2],
        ]
        e = [mu, g0, Decimal(2) * g1 + g0 * g0]
        d = [mu, mu * g0, mu * g1 + g0 * g0]
        B = [
            [one, g0, m2],
            [g0, g0 * g0, g0 * m2],
            [m2, g0 * (g1 + g0), g1 * g1 + g1 * g0 * g0 + g0 * g0 * g0],
        ]
        rr = point_outer(r, r)
        sigma_r = point_scalar_mul(
            one / mu,
            point_add(
                point_add(point_sub(point_sub(A, point_outer(e, r)), point_outer(r, e)), point_scalar_mul(nu, rr)),
                point_add(point_sub(B, point_outer(d, r)), point_sub(point_transpose(B), point_outer(r, d))),
            ),
        )
        r0, r1, r2 = r
        Dq = r1 - r0 * r0
        E = r2 - r0 * r0
        lam = E / Dq
        a = r1 / r0
        lambda0 = -Decimal(2) * r0 * (r1 - r2) / (Dq * Dq)
        lambda1 = -E / (Dq * Dq)
        lambda2 = one / Dq
        J = [
            [a / r0 + lambda0, -one / r0 + lambda1, lambda2],
            [
                one - lam + a / r0 + (one - r0) * lambda0,
                -one / r0 + (one - r0) * lambda1,
                (one - r0) * lambda2,
            ],
        ]
        sigma = point_matmul(point_matmul(J, sigma_r), point_transpose(J))
        tr = sigma[0][0] + sigma[1][1]
        det = sigma[0][0] * sigma[1][1] - sigma[0][1] * sigma[1][0]
        t = [one, z]
        sigt = [sigma[0][0] * t[0] + sigma[0][1] * t[1], sigma[1][0] * t[0] + sigma[1][1] * t[1]]
        return {"sigma": sigma, "trace": tr, "det": det, "sigma_times_tangent": sigt}


def diagonal_covariance(z_text: str, prec: int = 90):
    getcontext().prec = prec
    z = Interval(z_text)
    one = Interval(1)

    # This certificate encloses theta=-log(z). For the worked rational z=1/2,
    # the bracket below is the standard 80-digit enclosure of log(2).
    if z_text == "0.5" or z_text == "1/2":
        theta = Interval(
            "0.69314718055994530941723212145817656807550013436025525412068000949339362196969471",
            "0.69314718055994530941723212145817656807550013436025525412068000949339362196969472",
        )
        z = Interval("0.5")
    else:
        raise ValueError(
            "This transcript helper ships only the worked certificate z=1/2. "
            "For another z, supply a certified outward-rounded interval for -log(z)."
        )

    omz = one - z
    g0 = omz - theta * z
    g1 = z * (omz * (one + theta) - theta * z)
    mu = one / omz + theta * z / (omz * omz)
    nu = (one + z) / (omz * omz) + theta * z * (Interval(3) + z) / (omz * omz * omz)
    m2 = g1 + g0 * g0
    r = [one / mu, g0 / mu, m2 / mu]

    A = [
        [one, g0, m2],
        [g0, g0, g0 * g0],
        [m2, g0 * g0, m2],
    ]
    e = [mu, g0, Interval(2) * g1 + g0 * g0]
    d = [mu, mu * g0, mu * g1 + g0 * g0]
    B = [
        [one, g0, m2],
        [g0, g0 * g0, g0 * m2],
        [m2, g0 * (g1 + g0), g1 * g1 + g1 * g0 * g0 + g0 * g0 * g0],
    ]
    Br = transpose(B)
    rr = outer(r, r)
    sigma_r = scalar_mul(
        one / mu,
        add(
            add(sub(sub(A, outer(e, r)), outer(r, e)), scalar_mul(nu, rr)),
            add(sub(B, outer(d, r)), sub(Br, outer(r, d))),
        ),
    )

    r0, r1, r2 = r
    Dq = r1 - r0 * r0
    E = r2 - r0 * r0
    lam = E / Dq

    # Phi_1 = 1 - r1/r0 + lambda;
    # Phi_2 = r0(1-lambda) - r1/r0 + lambda.
    dlambda = [
        -(Interval(2) * r0 * (r1 - r2)) / (Dq * Dq),
        -E / (Dq * Dq),
        one / Dq,
    ]
    row1 = [dlambda[0] + r1 / (r0 * r0), dlambda[1] - one / r0, dlambda[2]]
    row2 = [
        one + r1 / (r0 * r0) - lam + (one - r0) * dlambda[0],
        -one / r0 + (one - r0) * dlambda[1],
        (one - r0) * dlambda[2],
    ]
    J = [row1, row2]
    sigma = matmul(matmul(J, sigma_r), transpose(J))
    tr = sigma[0][0] + sigma[1][1]
    det = sigma[0][0] * sigma[1][1] - sigma[0][1] * sigma[1][0]
    t = [one, z]
    sigt = [sigma[0][0] * t[0] + sigma[0][1] * t[1], sigma[1][0] * t[0] + sigma[1][1] * t[1]]
    norm_sigt = sigt[0].sq() + sigt[1].sq()
    return {
        "z": z_text,
        "precision_decimal_digits": prec,
        "substitution_values": {
            "z": "1/2",
            "theta": "log(2)",
            "g0": "(1-log(2))/2",
            "g1": "1/4",
            "mu": "2+2*log(2)",
            "m2": "g1+g0^2",
        },
        "theta_interval": theta.to_json(),
        "sigma_interval": [[x.to_json() for x in row] for row in sigma],
        "I_tau": tr.to_json(),
        "I_det": det.to_json(),
        "trace_interval": tr.to_json(),
        "determinant_interval": det.to_json(),
        "sigma_times_tangent_interval": [x.to_json() for x in sigt],
        "sigma_times_tangent_norm2_interval": norm_sigt.to_json(),
        "branch": "full_rank" if det.lo > 0 else "inconclusive",
        "full_rank_margin_lower_bound": str(det.lo) if det.lo > 0 else None,
    }


def run_formula_self_test():
    data = diagonal_covariance("0.5")
    point = printed_formula_point_values()
    validate_certificate_against_printed_formulas(data, point)


def interval_contains(interval, value):
    lo, hi = map(Decimal, interval)
    return lo <= value <= hi


def intervals_overlap(left, right):
    left_lo, left_hi = map(Decimal, left)
    right_lo, right_hi = map(Decimal, right)
    return left_lo <= right_hi and right_lo <= left_hi


def canonical_json(data):
    return json.dumps(data, indent=2) + "\n"


def validate_certificate_against_printed_formulas(data, point):
    sigma = data["sigma_interval"]
    for i in range(2):
        for j in range(2):
            expected = point["sigma"][i][j]
            if not interval_contains(sigma[i][j], expected):
                raise AssertionError(
                    f"Sigma[{i},{j}] interval {sigma[i][j]} does not contain "
                    f"the value obtained from the printed formulas, {expected}"
                )
    for key, json_key in [("trace", "trace_interval"), ("det", "determinant_interval")]:
        if not interval_contains(data[json_key], point[key]):
            raise AssertionError(
                f"{json_key} {data[json_key]} does not contain the value "
                f"obtained from the printed formulas, {point[key]}"
            )
    if intervals_overlap(data["trace_interval"], STALE_TRACE_INTERVAL):
        raise AssertionError(
            "trace_interval overlaps the stale manuscript interval "
            f"{STALE_TRACE_INTERVAL}"
        )
    if intervals_overlap(data["determinant_interval"], STALE_DETERMINANT_INTERVAL):
        raise AssertionError(
            "determinant_interval overlaps the stale manuscript interval "
            f"{STALE_DETERMINANT_INTERVAL}"
        )


class DiagonalBranchCertificateTests(unittest.TestCase):
    def test_transcript_records_referee_substitution_values(self):
        data = diagonal_covariance("0.5")
        self.assertEqual(data["substitution_values"]["z"], "1/2")
        self.assertEqual(data["substitution_values"]["theta"], "log(2)")
        self.assertEqual(data["substitution_values"]["g0"], "(1-log(2))/2")
        self.assertEqual(data["substitution_values"]["g1"], "1/4")
        self.assertEqual(data["substitution_values"]["mu"], "2+2*log(2)")
        self.assertEqual(data["substitution_values"]["m2"], "g1+g0^2")

    def test_direct_formula_values_round_to_manuscript_certificate_numbers(self):
        point = printed_formula_point_values()
        quant = Decimal("0.0000000000001")
        for i in range(2):
            for j in range(2):
                self.assertEqual(
                    str(point["sigma"][i][j].quantize(quant)),
                    EXPECTED_ROUNDED["sigma"][i][j],
                )
        self.assertEqual(str(point["trace"].quantize(quant)), EXPECTED_ROUNDED["trace"])
        self.assertEqual(
            str(point["det"].quantize(Decimal("0.00000000000001"))),
            EXPECTED_ROUNDED["det"],
        )

    def test_certificate_encloses_values_evaluated_from_printed_formulas(self):
        data = diagonal_covariance("0.5")
        point = printed_formula_point_values()
        validate_certificate_against_printed_formulas(data, point)

    def test_stored_json_encloses_values_evaluated_from_printed_formulas(self):
        regenerated = diagonal_covariance("0.5")
        point = printed_formula_point_values()
        with TRANSCRIPT_PATH.open(encoding="utf-8-sig") as transcript_file:
            data = json.load(transcript_file)
        self.assertEqual(canonical_json(data), canonical_json(regenerated))
        validate_certificate_against_printed_formulas(data, point)

    def test_stale_trace_and_determinant_intervals_are_not_accepted(self):
        data = diagonal_covariance("0.5")
        stale = dict(data)
        stale["trace_interval"] = [str(STALE_TRACE_INTERVAL[0]), str(STALE_TRACE_INTERVAL[1])]
        stale["I_tau"] = stale["trace_interval"]
        stale["determinant_interval"] = [
            str(STALE_DETERMINANT_INTERVAL[0]),
            str(STALE_DETERMINANT_INTERVAL[1]),
        ]
        stale["I_det"] = stale["determinant_interval"]
        point = printed_formula_point_values()
        with self.assertRaises(AssertionError):
            validate_certificate_against_printed_formulas(stale, point)


if __name__ == "__main__":
    if "--test" in sys.argv:
        unittest.main(argv=[sys.argv[0]])
        sys.exit(0)
    run_formula_self_test()
    data = diagonal_covariance("0.5")
    print(json.dumps(data, indent=2))
