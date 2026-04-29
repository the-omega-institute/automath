import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-escort-tv-identifiable-limit-distance`. -/
theorem paper_xi_foldbin_escort_tv_identifiable_limit_distance
    (theta : ℝ → ℝ)
    (hstrict : ∀ {p q : ℝ}, 0 ≤ p → 0 ≤ q → p < q → theta q < theta p)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : theta p = theta q) :
    p = q := by
  by_contra hpq
  rcases lt_or_gt_of_ne hpq with hp_lt_q | hq_lt_p
  · have hlt : theta q < theta p := hstrict hp hq hp_lt_q
    linarith
  · have hlt : theta p < theta q := hstrict hq hp hq_lt_p
    linarith

end Omega.Zeta
