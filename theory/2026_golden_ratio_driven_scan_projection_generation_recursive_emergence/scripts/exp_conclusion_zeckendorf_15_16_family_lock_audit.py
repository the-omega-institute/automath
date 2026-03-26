from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple


def _fib_upto(n: int) -> List[int]:
    # Standard: F_0=0,F_1=1
    F = [0, 1]
    for _ in range(2, n + 1):
        F.append(F[-1] + F[-2])
    return F


def _zeckendorf_indices(N: int, F: List[int]) -> List[int]:
    """
    Return indices (>=2) of Zeckendorf decomposition of N using Fibonacci numbers F_k
    with F_0=0,F_1=1 (so F_2=1,F_3=2,...). Greedy is canonical.
    """
    if N < 0:
        raise ValueError("N must be nonnegative")
    if N == 0:
        return []
    idxs: List[int] = []
    k = len(F) - 1
    while N > 0:
        while k >= 2 and F[k] > N:
            k -= 1
        if k < 2:
            raise RuntimeError("F list too short for greedy")
        idxs.append(k)
        N -= F[k]
        k -= 2  # enforce non-adjacent
    return idxs


def _indices_sum(idxs: List[int], F: List[int]) -> int:
    return sum(F[i] for i in idxs)


def _nonadjacent(idxs: List[int]) -> bool:
    s = sorted(idxs, reverse=True)
    return all(s[i] - s[i + 1] >= 2 for i in range(len(s) - 1))


@dataclass(frozen=True)
class Check:
    name: str
    ok: bool
    detail: Dict[str, object]


def main() -> None:
    max_n = 60
    max_m = 80
    F = _fib_upto(max(max_n + 10, max_m + 10))
    checks: List[Check] = []

    # Theorem: closed identities and Zeckendorf match for n>=8
    for n in range(8, max_n + 1):
        lhs15 = 15 * F[n]
        rhs15_idxs = [n + 5, n + 2, n, n - 3, n - 6]
        rhs15 = _indices_sum(rhs15_idxs, F)
        z15 = _zeckendorf_indices(lhs15, F)
        checks.append(
            Check(
                name=f"15Fn_closed_and_zeckendorf_n={n}",
                ok=(lhs15 == rhs15 and _nonadjacent(rhs15_idxs) and z15 == rhs15_idxs),
                detail={"lhs": lhs15, "rhs": rhs15, "z": z15, "rhs_indices": rhs15_idxs},
            )
        )

        lhs16 = 16 * F[n]
        rhs16_idxs = [n + 5, n + 3, n - 1, n - 6]
        rhs16 = _indices_sum(rhs16_idxs, F)
        z16 = _zeckendorf_indices(lhs16, F)
        checks.append(
            Check(
                name=f"16Fn_closed_and_zeckendorf_n={n}",
                ok=(lhs16 == rhs16 and _nonadjacent(rhs16_idxs) and z16 == rhs16_idxs),
                detail={"lhs": lhs16, "rhs": rhs16, "z": z16, "rhs_indices": rhs16_idxs},
            )
        )

    # Corollary: cross-resolution decompositions for m>=10
    for m in range(10, 50):
        # |X_m^{bdry}| = F_{m-2}, |X_k|=F_{k+2}
        lhs15 = 15 * F[m - 2]
        rhs15 = F[(m + 1) + 2] + F[(m - 2) + 2] + F[(m - 4) + 2] + F[(m - 7) + 2] + F[(m - 10) + 2]
        lhs16 = 16 * F[m - 2]
        rhs16 = F[(m + 1) + 2] + F[(m - 1) + 2] + F[(m - 5) + 2] + F[(m - 10) + 2]
        checks.append(
            Check(
                name=f"cross_resolution_15_m={m}",
                ok=(lhs15 == rhs15),
                detail={"lhs": lhs15, "rhs": rhs15},
            )
        )
        checks.append(
            Check(
                name=f"cross_resolution_16_m={m}",
                ok=(lhs16 == rhs16),
                detail={"lhs": lhs16, "rhs": rhs16},
            )
        )

    # Carry identity for n>=5
    for n in range(5, max_n + 1):
        lhs = F[n + 2] + 2 * F[n] + F[n - 3]
        rhs = F[n + 3] + F[n - 1]
        checks.append(Check(name=f"carry_identity_n={n}", ok=(lhs == rhs), detail={"lhs": lhs, "rhs": rhs}))

    # Resolution lock: 15F_{m-2} contains F_4 and F_6 iff m=6 (m>=6)
    hits: List[int] = []
    for m in range(6, 50):
        n = m - 2
        z = _zeckendorf_indices(15 * F[n], F)
        if 4 in z and 6 in z:
            hits.append(m)
    checks.append(Check(name="resolution_lock_m6_unique", ok=(hits == [6]), detail={"hits": hits}))

    # Top term: largest summand of 15F_{m-2} is F_{m+3} for m>=6
    ok_top = True
    bad: List[Tuple[int, int, int]] = []
    for m in range(6, max_m):
        z = _zeckendorf_indices(15 * F[m - 2], F)
        top_idx = z[0] if z else -1
        if top_idx != m + 3:
            ok_top = False
            bad.append((m, top_idx, m + 3))
    checks.append(Check(name="top_term_is_F_{m+3}_m>=6", ok=ok_top, detail={"bad": bad[:10]}))

    # delta=34 equivalence: top term equals F_9 iff m=6
    delta = 34
    delta_idx = 9  # F_9=34
    candidates = []
    for m in range(6, max_m):
        z = _zeckendorf_indices(15 * F[m - 2], F)
        if z and z[0] == delta_idx:
            candidates.append(m)
    checks.append(Check(name="delta34_top_term_iff_m6", ok=(candidates == [6]), detail={"candidates": candidates, "delta": delta}))

    out = {
        "max_n": max_n,
        "all_ok": all(c.ok for c in checks),
        "checks": [asdict(c) for c in checks],
    }
    export_dir = Path(__file__).resolve().parents[1] / "artifacts" / "export"
    export_dir.mkdir(parents=True, exist_ok=True)
    out_path = export_dir / "conclusion_zeckendorf_15_16_family_lock_audit.json"
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    assert out["all_ok"], "One or more conclusion Zeckendorf 15/16 audits failed"


if __name__ == "__main__":
    main()

