import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9o-escort-fiberinfo-constantterm-inversion`. -/
theorem paper_xi_time_part9o_escort_fiberinfo_constantterm_inversion (logPhi : ℝ)
    (a c inv : ℝ → ℝ) (hlog : 0 < logPhi) (ha_nonneg : ∀ q, 0 ≤ a q)
    (ha_strict : ∀ ⦃q r⦄, 0 ≤ q → q < r → a q < a r)
    (hc : ∀ q, 0 ≤ q → c q = logPhi / (1 + a q))
    (hinv : ∀ q, 0 ≤ q → inv (c q) = q) :
    (∀ q, 0 ≤ q → c q = logPhi / (1 + a q)) ∧
      (∀ ⦃q r⦄, 0 ≤ q → q < r → c r < c q) ∧
        (∀ q, 0 ≤ q → inv (c q) = q) := by
  refine ⟨hc, ?_, hinv⟩
  intro q r hq hqr
  have hden_q : 0 < 1 + a q := by linarith [ha_nonneg q]
  have hden_lt : 1 + a q < 1 + a r := by linarith [ha_strict hq hqr]
  rw [hc q hq, hc r (le_trans hq hqr.le)]
  exact div_lt_div_of_pos_left hlog hden_q hden_lt

end Omega.Zeta
