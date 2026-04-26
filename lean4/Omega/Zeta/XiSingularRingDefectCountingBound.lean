import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-singular-ring-defect-counting-bound`. -/
theorem paper_xi_singular_ring_defect_counting_bound (Delta R eta count : ℝ) (heta : 0 < eta)
    (hbound : count * (eta / (R ^ 2 + 2 * eta)) ≤ Delta) :
    count ≤ Delta * ((R ^ 2 + 2 * eta) / eta) := by
  let denom : ℝ := R ^ 2 + 2 * eta
  have hdenom_pos : 0 < denom := by
    dsimp [denom]
    positivity
  have hfactor_nonneg : 0 ≤ denom / eta := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_right hbound hfactor_nonneg
  have heta_ne : eta ≠ 0 := ne_of_gt heta
  have hdenom_ne : denom ≠ 0 := ne_of_gt hdenom_pos
  have hcancel : (eta / denom) * (denom / eta) = 1 := by
    field_simp [heta_ne, hdenom_ne]
  have hcount_eq : count * (eta / denom) * (denom / eta) = count := by
    rw [mul_assoc, hcancel, mul_one]
  simpa [denom, hcount_eq, mul_assoc] using hscaled

end Omega.Zeta
