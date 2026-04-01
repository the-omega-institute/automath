from __future__ import annotations

from typing import Dict, Tuple

from common import R, assert_equal, compute_parry_measure, pair_sofic_adjacency


def run() -> str:
    """
    Verify the exact bulk joint law in Sec.4.3 via the 4-state sofic presentation.
    """
    A = pair_sofic_adjacency()
    pm = compute_parry_measure(A)

    # Basic spectral facts
    assert_equal(pm.lam, 2, "Perron 根应为 2。")

    # Labeled edges (with multiplicities embedded in A):
    # state 0: 0->0 label 00; 0->1 label 01; 0->3 label 11
    # state 1: 1->2 label 10
    # state 2: 2->0 label 10; 2->1 label 00; 2->1 label 11 (two parallel edges)
    # state 3: 3->0 label 00
    labeled_edges = [
        (0, 0, (0, 0)),
        (0, 1, (0, 1)),
        (0, 3, (1, 1)),
        (1, 2, (1, 0)),
        (2, 0, (1, 0)),
        (2, 1, (0, 0)),
        (2, 1, (1, 1)),
        (3, 0, (0, 0)),
    ]

    # Symbol probabilities on edges under Parry measure:
    # prob(edge i->j) = pi_i * P_{ij} / A_{ij} (split uniformly among parallel edges)
    prob: Dict[Tuple[int, int], object] = {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}
    for i, j, label in labeled_edges:
        mult = int(A[i, j])
        p_edge = pm.pi[i] * pm.P[i, j] / mult
        prob[label] = prob[label] + p_edge

    expected = {
        (0, 0): R(7, 18),
        (0, 1): R(1, 9),
        (1, 0): R(1, 3),
        (1, 1): R(1, 6),
    }
    for k, v in expected.items():
        assert_equal(prob[k], v, f"符号概率 P(X,Y) 不匹配：{k}")

    # Derived marginals
    p_mismatch = prob[(0, 1)] + prob[(1, 0)]
    p_y1 = prob[(0, 1)] + prob[(1, 1)]
    assert_equal(p_mismatch, R(4, 9), "P(X!=Y) 应为 4/9。")
    assert_equal(p_y1, R(5, 18), "P(Y=1) 应为 5/18。")

    return "Sofic joint law OK (7/18, 1/9, 1/3, 1/6; mismatch 4/9; P(Y=1)=5/18)"


if __name__ == "__main__":  # pragma: no cover
    print(run())

