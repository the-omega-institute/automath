from __future__ import annotations

from common import R, assert_equal, assert_simplify_zero, compute_parry_measure, pair_sofic_adjacency, sp


def _edge_chain_for_discrepancy(P: sp.Matrix, pi: sp.Matrix):
    """
    Build the 7-edge-type Markov chain used to compute covariances of the discrepancy indicator.
    Each edge type is (start_state, end_state, g), with g=1 iff label is 01 or 10.

    Note: we merge the two parallel edges 2->1 (labels 00 and 11) into a single type since g=0 for both.
    This preserves all second-order statistics of g.
    """
    # Edge types: (s,t,g)
    edges = [
        (0, 0, 0),  # 00
        (0, 1, 1),  # 01
        (0, 3, 0),  # 11
        (1, 2, 1),  # 10
        (2, 0, 1),  # 10
        (2, 1, 0),  # 00/11 merged
        (3, 0, 0),  # 00
    ]
    m = len(edges)

    # Edge transition matrix Q: from e=(s->t) to e'=(t->u) with prob P[t,u]
    Q = sp.Matrix.zeros(m, m)
    for i, (_, t, _) in enumerate(edges):
        for j, (s2, u, _) in enumerate(edges):
            if s2 == t:
                Q[i, j] = P[t, u]

    # Stationary distribution over edge types: w_e = pi_s * P[s,t]
    w = sp.Matrix([0] * m)
    for i, (s, t, _) in enumerate(edges):
        w[i] = sp.simplify(pi[s] * P[s, t])

    # Observable g on edges
    G = sp.Matrix([g for _, _, g in edges])

    return edges, Q, w, G


def run() -> str:
    """
    Verify:
      - covariance closed form (including the (-1/2)^j and j(-1/2)^j modes),
      - Green--Kubo variance sigma^2 = 118/243,
      - rational PSD formula S(omega) and S(0)=118/243.
    """
    A = pair_sofic_adjacency()
    pm = compute_parry_measure(A)
    assert_equal(pm.lam, 2, "Perron 根应为 2。")

    edges, Q, w, G = _edge_chain_for_discrepancy(pm.P, pm.pi)
    ones = sp.Matrix([1] * len(edges))
    mu = sp.simplify((w.T * G)[0])
    assert_equal(mu, R(4, 9), "差异指示过程的均值应为 4/9。")

    Gc = sp.simplify(G - mu * ones)

    # Compute covariances c_j = Cov(Delta_0, Delta_j) via edge chain
    def cov_j(j: int):
        v = (Q**j) * Gc
        return sp.simplify((w.T * sp.Matrix([Gc[i] * v[i] for i in range(len(edges))]))[0])

    c0 = cov_j(0)
    assert_equal(c0, R(20, 81), "c0 应为 20/81。")

    # Verify closed form for j>=1:
    # c_j = 2^{-j} * ( 1/8 + (-1)^j * (7/648 + j/108) ).
    for j in range(1, 60):
        cj = cov_j(j)
        closed = sp.simplify(
            (R(1, 2) ** j)
            * (R(1, 8) + ((-1) ** j) * (R(7, 648) + R(j, 108)))
        )
        assert_equal(cj, closed, f"协方差闭式不匹配：j={j}")

    # Green--Kubo asymptotic variance via fundamental matrix on centered chain
    Pi = ones * w.T  # projector
    M = Q - Pi
    S = (sp.eye(len(edges)) - M).inv()  # sum_{k>=0} (Q-Pi)^k

    sum_ge0 = sp.simplify(S * Gc)  # = sum_{k>=0} Q^k Gc (since Pi*Gc=0)
    sum_ge1 = sp.simplify(sum_ge0 - Gc)
    sum_c_ge1 = sp.simplify((w.T * sp.Matrix([Gc[i] * sum_ge1[i] for i in range(len(edges))]))[0])
    sigma2 = sp.simplify(c0 + 2 * sum_c_ge1)
    assert_equal(sigma2, R(118, 243), "CLT 渐近方差 sigma^2 应为 118/243。")

    # PSD derivation from closed-form covariance series (symbolic)
    omega = sp.Symbol("omega", real=True)
    r = sp.Symbol("r", real=True)
    D = 1 - 2 * r * sp.cos(omega) + r**2
    S1 = (r * sp.cos(omega) - r**2) / D  # sum_{j>=1} r^j cos(j omega)
    Sj = sp.simplify(r * sp.diff(S1, r))  # sum_{j>=1} j r^j cos(j omega)

    rpos = R(1, 2)
    rneg = -R(1, 2)
    S_cos_pos = sp.simplify(S1.subs({r: rpos}))
    S_cos_neg = sp.simplify(S1.subs({r: rneg}))
    S_j_cos_neg = sp.simplify(Sj.subs({r: rneg}))

    S_omega = sp.simplify(
        c0
        + 2
        * (
            R(1, 8) * S_cos_pos
            + R(7, 648) * S_cos_neg
            + R(1, 108) * S_j_cos_neg
        )
    )
    S_omega = sp.together(S_omega)

    expected = sp.together(
        2
        * (
            32 * sp.cos(omega) ** 3
            + 12 * sp.cos(omega) ** 2
            - 116 * sp.cos(omega)
            - 105
        )
        / (9 * (4 * sp.cos(omega) - 5) * (4 * sp.cos(omega) + 5) ** 2)
    )
    assert_simplify_zero(S_omega - expected, "功率谱闭式与期望有理式不一致。")

    S0 = sp.simplify(S_omega.subs({omega: 0}))
    assert_equal(S0, R(118, 243), "S(0) 应等于 118/243（Green--Kubo/Wiener--Khinchin 一致性）。")

    return "Spectrum OK (cov closed form; sigma^2=118/243; PSD rational; S(0) matches)"


if __name__ == "__main__":  # pragma: no cover
    print(run())

