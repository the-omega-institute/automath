from __future__ import annotations

from common import R, assert_equal, assert_simplify_zero, sp


def _squarefree_part(n: int) -> int:
    if n == 0:
        return 0
    sign = -1 if n < 0 else 1
    n = abs(n)
    fac = sp.factorint(n)
    out = 1
    for p, e in fac.items():
        if e % 2 == 1:
            out *= p
    return sign * out


def run() -> str:
    """
    Verify:
      - Disc_lambda Pi(lambda,y) factorization in Sec.6.3,
      - q=2 fingerprint: Disc(P2)=148, squarefree part 37.
    """
    lam, y = sp.symbols("lam y")

    Pi = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)
    disc = sp.discriminant(Pi, lam)
    disc_fact = sp.factor(disc)
    expected = -y * (y - 1) * (256 * y**3 + 411 * y**2 + 165 * y + 32)

    assert_simplify_zero(disc_fact - expected, "Disc_lambda Pi(lambda,y) 分解不匹配。")

    cubic = 256 * y**3 + 411 * y**2 + 165 * y + 32
    roots = [complex(z) for z in sp.nroots(cubic, n=20)]
    neg_real = [z.real for z in roots if abs(z.imag) < 1e-10 and z.real < 0]
    if len(neg_real) != 1:
        raise AssertionError(f"预期 cubic 只有一个负实根，实际找到：{neg_real}（roots={roots}）")
    y_LY = neg_real[0]
    if abs(y_LY - (-1.13445)) > 5e-4:
        raise AssertionError(f"y_LY 数值不在预期范围：got {y_LY}, expected about -1.13445")

    # q=2 fingerprint
    P2 = lam**3 - 2 * lam**2 - 2 * lam + 2
    disc2 = int(sp.discriminant(P2, lam))
    assert_equal(disc2, 148, "Disc(P2) 应为 148。")
    sf = _squarefree_part(disc2)
    assert_equal(sf, 37, "Disc(P2) 的平方自由部分应为 37。")

    return "Discriminants OK (Disc quartic factorization; y_LY approx; Disc(P2)=148, sf=37)"


if __name__ == "__main__":  # pragma: no cover
    print(run())

