from __future__ import annotations

from common import assert_equal, fib_sequence, gauge_anomaly_Gm, omega_star


def run() -> str:
    """
    Verify the explicit worst-case family omega^* achieves G_m(omega^*) = m.
    We check this for a reasonably large range of m (finite but strong regression test).
    """
    max_m = 400
    # Need Fibonacci numbers up to index (max_m+1)+3 safely
    F = fib_sequence(max_m + 10)

    for m in range(1, max_m + 1):
        w = omega_star(m)
        g = gauge_anomaly_Gm(m, w, F)
        if g != m:
            raise AssertionError(
                f"最坏情形族验证失败：m={m}, G_m={g}, 期待 {m}, omega^*={''.join(map(str,w))}"
            )

    return f"Worst-case OK (omega^* gives G_m=m for m=1..{max_m})"


if __name__ == "__main__":  # pragma: no cover
    print(run())

