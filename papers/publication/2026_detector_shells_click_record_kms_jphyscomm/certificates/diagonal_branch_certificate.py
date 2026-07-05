from __future__ import annotations

import json
from decimal import Decimal, getcontext, localcontext, ROUND_FLOOR, ROUND_CEILING


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
    dE = [-(r1), -r0, one]
    dD = [-(Interval(2) * r0), one, Interval(0)]
    dlambda = [(dE[i] * Dq - E * dD[i]) / (Dq * Dq) for i in range(3)]
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


if __name__ == "__main__":
    data = diagonal_covariance("0.5")
    print(json.dumps(data, indent=2))
