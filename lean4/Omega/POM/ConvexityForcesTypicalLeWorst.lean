import Mathlib

namespace Omega.POM

/-- Paper label: `prop:pom-convexity-forces-typical-le-worst`. -/
theorem paper_pom_convexity_forces_typical_le_worst
    (logR : ℝ → ℝ) (yStar lambdaInfR lambdaInf : ℝ)
    (hSupport :
      ∀ q : ℝ, 1 < q → logR 1 + (q - 1) * yStar ≤ logR q)
    (hSlopeUpper :
      ∀ eps : ℝ, 0 < eps →
        ∃ Q : ℝ, ∀ q : ℝ, Q ≤ q → logR q / q ≤ lambdaInfR + eps)
    (hBoundary : lambdaInfR = lambdaInf) :
    yStar ≤ lambdaInf := by
  by_contra hnot
  have hlt : lambdaInfR < yStar := by
    have hltBoundary : lambdaInf < yStar := lt_of_not_ge hnot
    rwa [hBoundary]
  let gap : ℝ := yStar - lambdaInfR
  have hgap_pos : 0 < gap := sub_pos.mpr hlt
  have heps_pos : 0 < gap / 4 := by positivity
  obtain ⟨Q, hUpper⟩ := hSlopeUpper (gap / 4) heps_pos
  let q : ℝ := max Q (max 2 (4 * |logR 1 - yStar| / gap + 1))
  have hQq : Q ≤ q := by
    exact le_max_left Q (max 2 (4 * |logR 1 - yStar| / gap + 1))
  have htwoq : 2 ≤ q := by
    exact le_trans (le_max_left 2 (4 * |logR 1 - yStar| / gap + 1)) (le_max_right Q _)
  have hqpos : 0 < q := by linarith
  have hqone : 1 < q := by linarith
  have hfrac_le_q : 4 * |logR 1 - yStar| / gap ≤ q := by
    have hstep : 4 * |logR 1 - yStar| / gap + 1 ≤ q := by
      exact le_trans (le_max_right 2 (4 * |logR 1 - yStar| / gap + 1)) (le_max_right Q _)
    linarith
  have habs_mul_le : 4 * |logR 1 - yStar| ≤ q * gap := by
    exact (div_le_iff₀ hgap_pos).mp hfrac_le_q
  have habs_div_le : |logR 1 - yStar| / q ≤ gap / 4 := by
    rw [div_le_iff₀ hqpos]
    nlinarith
  have hdivSupport :
      (logR 1 + (q - 1) * yStar) / q ≤ logR q / q := by
    exact div_le_div_of_nonneg_right (hSupport q hqone) (le_of_lt hqpos)
  have haffine :
      (logR 1 + (q - 1) * yStar) / q =
        yStar + (logR 1 - yStar) / q := by
    field_simp [ne_of_gt hqpos]
    ring
  have herror_lower : -(gap / 4) ≤ (logR 1 - yStar) / q := by
    have hneg :
        -(|logR 1 - yStar| / q) ≤ (logR 1 - yStar) / q := by
      have hneg' :
          (-|logR 1 - yStar|) / q ≤ (logR 1 - yStar) / q := by
        exact div_le_div_of_nonneg_right (neg_abs_le (logR 1 - yStar)) (le_of_lt hqpos)
      simpa [neg_div] using hneg'
    linarith
  have hlower :
      yStar - gap / 4 ≤ (logR 1 + (q - 1) * yStar) / q := by
    rw [haffine]
    linarith
  have hchain : yStar - gap / 4 ≤ lambdaInfR + gap / 4 := by
    exact le_trans hlower (le_trans hdivSupport (hUpper q hQq))
  linarith

end Omega.POM
