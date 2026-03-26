from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple


def _fib_upto(n: int) -> List[int]:
    # F_0=0,F_1=1, return F_0..F_n
    F = [0, 1]
    for _ in range(2, n + 1):
        F.append(F[-1] + F[-2])
    return F


def _a_counts(m: int) -> Tuple[List[int], int, int, List[int]]:
    """
    a[s] = #{omega in {0,1}^m : sum_{k=1..m} omega_k F_{k+1} = s}
    Returns (a, T_m, M_m, F).
    """
    F = _fib_upto(m + 3)
    weights = [F[k + 1] for k in range(1, m + 1)]  # k=1..m -> F_{k+1}
    T_m = sum(weights)
    M_m = F[m + 2]
    a = [0] * (T_m + 1)
    a[0] = 1
    for w in weights:
        for s in range(T_m - w, -1, -1):
            if a[s]:
                a[s + w] += a[s]
    return a, T_m, M_m, F


def _A_closed(m: int) -> int:
    if m % 2 == 0:
        return (4 ** (m // 2) - 1) // 3
    return (2 * (4 ** ((m - 1) // 2) - 1)) // 3


def _alt_solution_Mm_minus_one(m: int, F: List[int]) -> List[int]:
    # omega indexed 1..m; return list length m with omega_1..omega_m
    omega = [0] * (m + 1)
    for k in range(m, 0, -1):
        omega[k] = 1 if (m - k) % 2 == 0 else 0
    # If m odd, pattern ends with ...0,1 in (omega_m,...,omega_1) notation,
    # which corresponds to omega_1=1. Current rule already gives omega_1=1.
    # If m even, omega_1=0. This matches the stated patterns.
    s = sum(omega[k] * F[k + 1] for k in range(1, m + 1))
    assert s == F[m + 2] - 1
    return omega[1:]


@dataclass(frozen=True)
class Check:
    name: str
    ok: bool
    detail: Dict[str, object]


def main() -> None:
    max_m = 26
    checks: List[Check] = []
    for m in range(2, max_m + 1):
        a, T_m, M_m, F = _a_counts(m)
        A = sum(a[M_m:])
        A_expected = _A_closed(m)
        checks.append(
            Check(
                name=f"A_m_closed_form_m={m}",
                ok=(A == A_expected),
                detail={"A": A, "A_expected": A_expected, "M_m": M_m, "T_m": T_m},
            )
        )

        # Top-two Zeckendorf digit counts via interval characterization
        count_01 = sum(a[M_m:])  # N >= F_{m+2}
        count_10 = sum(a[F[m + 1] : M_m])  # F_{m+1} <= N < F_{m+2}
        count_00 = sum(a[: F[m + 1]])  # N < F_{m+1}
        count_10_expected = (2**m) - 2 * A - 1
        checks.append(
            Check(
                name=f"top_two_trisect_counts_m={m}",
                ok=(
                    count_01 == A
                    and count_00 == A + 1
                    and count_10 == count_10_expected
                    and count_00 + count_10 + count_01 == 2**m
                ),
                detail={
                    "count_01": count_01,
                    "count_10": count_10,
                    "count_00": count_00,
                    "A": A,
                    "count_10_expected": count_10_expected,
                    "total": count_00 + count_10 + count_01,
                    "two_pow_m": 2**m,
                },
            )
        )

        # Endpoint uniqueness at M_m-1, and alternating pattern is valid
        alt = _alt_solution_Mm_minus_one(m, F)
        checks.append(
            Check(
                name=f"endpoint_Mm_minus_one_unique_m={m}",
                ok=(a[M_m - 1] == 1),
                detail={"a[M_m-1]": a[M_m - 1], "alt_solution_omega_1_to_m": alt},
            )
        )

        # Zero fiber size formula: f_m(0)=a(0)+a(M_m)=1+floor(m/2)
        B = a[M_m]
        checks.append(
            Check(
                name=f"zero_fiber_linear_m={m}",
                ok=(a[0] == 1 and B == (m // 2) and (a[0] + B) == 1 + (m // 2)),
                detail={"a0": a[0], "aM": B, "floor_m_over_2": m // 2, "f0": a[0] + B},
            )
        )

        # Reciprocity and reflection symmetry: f_m(r)=a(r)+a(M+r)=a(r)+a(F_{m+1}-2-r)
        Fm1_minus_2 = F[m + 1] - 2
        ok_recip = True
        ok_reflect = True
        for r in range(0, M_m):
            fr = a[r] + a[M_m + r] if (M_m + r) <= T_m else a[r]
            rhs = a[r] + (a[Fm1_minus_2 - r] if 0 <= (Fm1_minus_2 - r) <= T_m else 0)
            if fr != rhs:
                ok_recip = False
                break
        for r in range(0, Fm1_minus_2 + 1):
            fr = a[r] + a[M_m + r]
            fr_ref = a[Fm1_minus_2 - r] + a[M_m + (Fm1_minus_2 - r)]
            if fr != fr_ref:
                ok_reflect = False
                break
        checks.append(
            Check(
                name=f"reciprocity_and_reflection_m={m}",
                ok=(ok_recip and ok_reflect),
                detail={"M_m": M_m, "T_m": T_m, "F_{m+1}-2": Fm1_minus_2, "ok_recip": ok_recip, "ok_reflect": ok_reflect},
            )
        )

    out = {
        "max_m": max_m,
        "all_ok": all(c.ok for c in checks),
        "checks": [asdict(c) for c in checks],
    }
    export_dir = Path(__file__).resolve().parents[1] / "artifacts" / "export"
    export_dir.mkdir(parents=True, exist_ok=True)
    out_path = export_dir / "fold_zeckendorf_mod_topbits_audit.json"
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True), encoding="utf-8")
    assert out["all_ok"], "One or more Fold Zeckendorf mod/topbits audits failed"


if __name__ == "__main__":
    main()

