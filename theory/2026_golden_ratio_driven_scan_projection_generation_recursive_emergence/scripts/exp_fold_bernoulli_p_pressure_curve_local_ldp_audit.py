from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path

import numpy as np
import sympy as sp


STATE_A = 0
STATE_B = 1
STATE_C = 2
STATE_D = 3


def _Q_p(u: float, p: float) -> np.ndarray:
    """
    Tilted kernel Q_p(u) in state order (a,b,c,d).
    Base Parry kernel P(p):
      a -> a with q, a -> b with p^2, a -> d with p q
      b -> c with 1
      c -> a with q, c -> b with p
      d -> a with 1
    Mismatch edges g=1 are (a,b), (b,c), (c,a).
    """
    q = 1.0 - p
    Q = np.zeros((4, 4), dtype=float)
    Q[STATE_A, STATE_A] = q
    Q[STATE_A, STATE_B] = (p**2) * u
    Q[STATE_A, STATE_D] = p * q
    Q[STATE_B, STATE_C] = 1.0 * u
    Q[STATE_C, STATE_A] = q * u
    Q[STATE_C, STATE_B] = p
    Q[STATE_D, STATE_A] = 1.0
    return Q


def _perron_eig(Q: np.ndarray) -> tuple[float, np.ndarray, np.ndarray]:
    """
    Return (rho, r, ell) with ell^T r = 1.
    """
    evals, evecs = np.linalg.eig(Q)
    idx = int(np.argmax(np.real(evals)))
    rho = float(np.real(evals[idx]))
    r = np.real(evecs[:, idx])
    # ensure positivity orientation
    if r[np.argmax(np.abs(r))] < 0:
        r = -r

    evals_t, evecs_t = np.linalg.eig(Q.T)
    idx_t = int(np.argmax(np.real(evals_t)))
    ell = np.real(evecs_t[:, idx_t])
    if ell[np.argmax(np.abs(ell))] < 0:
        ell = -ell

    denom = float(ell @ r)
    ell = ell / denom
    return rho, r, ell


def _A_prefactor_numeric(u: float, p: float) -> float:
    Q = _Q_p(u, p)
    rho, r, ell = _perron_eig(Q)
    e_d = np.zeros(4, dtype=float)
    e_d[STATE_D] = 1.0
    ones = np.ones(4, dtype=float)
    return float((e_d @ r) * (ell @ ones))


def _A_prefactor_closed(u: float, p: float, rho: float) -> float:
    num1 = rho**2 - p * u
    num2 = (
        rho**3
        + (p**2 * (u - 1.0) + p) * rho**2
        + (p * u * (p * u - 1.0)) * rho
        - (p**2) * (1.0 - p) * u
    )
    den = (
        rho**6
        + p * (1.0 - p - 2.0 * u) * rho**4
        + 2.0 * (p**2) * (1.0 - p) * (u**3) * rho**3
        + (p**2) * (u**2 - 2.0 * u * (1.0 - p)) * rho**2
        + (p**3) * (1.0 - p) * (u**2)
    )
    return float((num1 * num2) / den)


def _pmf_direct(p: float, m: int) -> np.ndarray:
    """
    Direct DP for a_{m,k} = P(G_m=k | S_0=d) in the 4-state chain (a,b,c,d).
    Returns array of length m+1.
    """
    q = 1.0 - p
    # transitions: list of (to_state, prob, mismatch_increment)
    trans: list[list[tuple[int, float, int]]] = [[] for _ in range(4)]
    trans[STATE_A] = [(STATE_A, q, 0), (STATE_B, p**2, 1), (STATE_D, p * q, 0)]
    trans[STATE_B] = [(STATE_C, 1.0, 1)]
    trans[STATE_C] = [(STATE_A, q, 1), (STATE_B, p, 0)]
    trans[STATE_D] = [(STATE_A, 1.0, 0)]

    dp = np.zeros((4, m + 1), dtype=float)
    dp[STATE_D, 0] = 1.0
    for step in range(m):
        ndp = np.zeros((4, m + 1), dtype=float)
        for s in range(4):
            for k in range(step + 1):
                prob = dp[s, k]
                if prob == 0.0:
                    continue
                for t_state, t_prob, inc in trans[s]:
                    ndp[t_state, k + inc] += prob * t_prob
        dp = ndp
    return dp.sum(axis=0)


def _pmf_by_2d_recurrence(p: float, m: int) -> np.ndarray:
    """
    Compute a_{m,k} for fixed m via the 2D recurrence from the paper.
    """
    a = np.zeros((m + 1, m + 1), dtype=float)
    a[0, 0] = 1.0
    a[1, 0] = 1.0
    if m >= 2:
        a[2, 0] = 1.0 - p**2
        a[2, 1] = p**2
    if m >= 3:
        a[3, 0] = 1.0 - 2.0 * p**2 + p**3
        a[3, 1] = p**2 - p**3
        a[3, 2] = p**2

    def get(mm: int, kk: int) -> float:
        if mm < 0 or kk < 0:
            return 0.0
        if mm > m or kk > m:
            return 0.0
        return float(a[mm, kk])

    for mm in range(4, m + 1):
        for kk in range(0, mm + 1):
            a[mm, kk] = (
                (1.0 - p) * get(mm - 1, kk)
                + p * (1.0 - p) * get(mm - 2, kk)
                + p * get(mm - 2, kk - 1)
                - p * (1.0 - p) * get(mm - 3, kk - 1)
                + (p**2) * (1.0 - p) * get(mm - 3, kk - 3)
                - (p**2) * (1.0 - p) * get(mm - 4, kk - 1)
            )
    return a[m, : m + 1].copy()


def _P_theta(theta: float, p: float) -> float:
    u = math.exp(theta)
    rho, _, _ = _perron_eig(_Q_p(u, p))
    return math.log(rho)


def _P_prime(theta: float, p: float, h: float = 1e-5) -> float:
    return (_P_theta(theta + h, p) - _P_theta(theta - h, p)) / (2.0 * h)


def _P_second(theta: float, p: float, h: float = 2e-4) -> float:
    return (_P_theta(theta + h, p) - 2.0 * _P_theta(theta, p) + _P_theta(theta - h, p)) / (h * h)


def _solve_theta_for_s(p: float, s: float) -> float:
    # bisection using monotonicity of P'(theta)
    lo, hi = -12.0, 12.0
    flo = _P_prime(lo, p) - s
    fhi = _P_prime(hi, p) - s
    # widen if needed
    for _ in range(6):
        if flo <= 0.0 <= fhi:
            break
        lo -= 6.0
        hi += 6.0
        flo = _P_prime(lo, p) - s
        fhi = _P_prime(hi, p) - s
    if not (flo <= 0.0 <= fhi):
        raise RuntimeError("Failed to bracket theta for given s.")

    for _ in range(80):
        mid = 0.5 * (lo + hi)
        fmid = _P_prime(mid, p) - s
        if fmid > 0.0:
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi)


@dataclass(frozen=True)
class AuditResult:
    p: float
    pmf_recurrence_max_abs_error_m12: float
    pmf_recurrence_total_mass_error_m12: float
    trigonal_discriminant_symbolic_ok: bool
    perron_prefactor_rel_error: float
    local_ldp_ratio_m200: float
    local_ldp_inputs: dict


def main() -> None:
    paper_root = Path(__file__).resolve().parents[1]
    out_path = paper_root / "artifacts" / "export" / "fold_bernoulli_p_pressure_curve_local_ldp_audit.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)

    p = 0.37

    # 1) 2D recurrence vs direct DP
    m_check = 12
    pmf_d = _pmf_direct(p, m_check)
    pmf_r = _pmf_by_2d_recurrence(p, m_check)
    pmf_err = float(np.max(np.abs(pmf_d - pmf_r)))
    pmf_mass_err = float(abs(float(pmf_r.sum()) - 1.0))

    # 2) symbolic discriminant check
    z, w = sp.symbols("z w")
    p_sym = sp.Rational(37, 100)  # keep exact
    kappa = p_sym / (1 - p_sym)
    C = 1 - (1 - p_sym) * z - p_sym * (1 - p_sym) * z**2
    poly = w**3 + kappa * z * C * w - kappa * C
    disc = sp.factor(sp.discriminant(poly, w))
    disc_expected = sp.factor(-(kappa**2) * (C**2) * (4 * kappa * z**3 * C + 27))
    trig_ok = sp.simplify(disc - disc_expected) == 0

    # 3) Perron prefactor A_p(u) closed form check
    u0 = 1.7
    Q0 = _Q_p(u0, p)
    rho0, _, _ = _perron_eig(Q0)
    A_num = _A_prefactor_numeric(u0, p)
    A_cl = _A_prefactor_closed(u0, p, rho0)
    A_rel = float(abs(A_num - A_cl) / max(1e-14, abs(A_num)))

    # 4) local LDP numerical check at moderate m
    s = 0.58
    theta_s = _solve_theta_for_s(p, s)
    u_s = math.exp(theta_s)
    rho_s, _, _ = _perron_eig(_Q_p(u_s, p))
    P2 = _P_second(theta_s, p)
    if P2 <= 0:
        raise RuntimeError("Numerical P'' estimate not positive; increase h or adjust parameters.")
    A_s = _A_prefactor_closed(u_s, p, rho_s)

    m = 200
    k = int(round(s * m))
    pmf_m = _pmf_direct(p, m)
    a_mk = float(pmf_m[k])
    approx = (A_s / (u_s**k)) * (rho_s**m) / math.sqrt(2.0 * math.pi * m * P2)
    ratio = float(a_mk / approx) if approx > 0 else float("nan")

    res = AuditResult(
        p=p,
        pmf_recurrence_max_abs_error_m12=pmf_err,
        pmf_recurrence_total_mass_error_m12=pmf_mass_err,
        trigonal_discriminant_symbolic_ok=bool(trig_ok),
        perron_prefactor_rel_error=A_rel,
        local_ldp_ratio_m200=ratio,
        local_ldp_inputs={
            "s": s,
            "theta_s": theta_s,
            "u_s": u_s,
            "rho_s": rho_s,
            "P_second_est": P2,
            "m": m,
            "k": k,
            "a_mk": a_mk,
            "approx": approx,
        },
    )

    out_path.write_text(json.dumps(asdict(res), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()

