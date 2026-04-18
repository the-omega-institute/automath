import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete analytic-radius certificate for the pressure branch. The branch-radius witness is the
explicit value `R_θ = π / 3`. -/
structure PressureAnalyticRadiusData where
  R_theta : ℝ
  hR_theta : R_theta = Real.pi / 3

/-- `p⋆ = 6` is the sharp threshold when `R_θ` is compared with the unit-root modulus
`2π / p`. -/
def PressureAnalyticRadiusData.unitRootModulusThreshold
    (D : PressureAnalyticRadiusData) : Prop :=
  D.R_theta = Real.pi / 3 ∧
    ∀ p : ℕ, 5 ≤ p → (D.R_theta ≤ 2 * Real.pi / p ↔ p ≤ 6)

lemma pressure_two_pi_div_antitone {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    2 * Real.pi / q ≤ 2 * Real.pi / p := by
  have hnonneg : 0 ≤ 2 * Real.pi := by positivity
  exact div_le_div_of_nonneg_left hnonneg (by exact_mod_cast hp) (by exact_mod_cast hpq)

lemma pressure_pi_div_three_le_two_pi_div_five : Real.pi / 3 ≤ 2 * Real.pi / 5 := by
  nlinarith [Real.pi_pos]

lemma pressure_pi_div_three_eq_two_pi_div_six : Real.pi / 3 = 2 * Real.pi / 6 := by
  ring_nf

lemma pressure_two_pi_div_seven_lt_pi_div_three : 2 * Real.pi / 7 < Real.pi / 3 := by
  nlinarith [Real.pi_pos]

/-- Paper label: `cor:pressure-unit-root-modulus-threshold`.
The explicit branch-radius certificate is `R_θ = π / 3`; it lies below `2π / 5`, equals
`2π / 6`, and is already above `2π / 7`. Since `p ↦ 2π / p` decreases for positive `p`, the
sharp threshold is `p⋆ = 6`. -/
theorem paper_pressure_unit_root_modulus_threshold (D : PressureAnalyticRadiusData) :
    D.unitRootModulusThreshold := by
  refine ⟨D.hR_theta, ?_⟩
  intro p hp
  constructor
  · intro hthreshold
    by_contra hpgt
    have hge7 : 7 ≤ p := by omega
    have hmono : 2 * Real.pi / p ≤ 2 * Real.pi / 7 := by
      simpa using pressure_two_pi_div_antitone (p := 7) (q := p) (by norm_num) hge7
    have hradius : Real.pi / 3 ≤ 2 * Real.pi / p := by
      simpa [D.hR_theta] using hthreshold
    linarith [pressure_two_pi_div_seven_lt_pi_div_three, hmono, hradius]
  · intro hp6
    have hp_cases : p = 5 ∨ p = 6 := by omega
    rcases hp_cases with rfl | rfl
    · simpa [D.hR_theta] using pressure_pi_div_three_le_two_pi_div_five
    · simp [D.hR_theta, pressure_pi_div_three_eq_two_pi_div_six]

end

end Omega.SyncKernelWeighted
