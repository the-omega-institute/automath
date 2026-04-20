import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The second-order Poisson--Cauchy profile. -/
def xiPoissonSecondOrderProfile (y : ℝ) : ℝ :=
  (3 * y ^ 2 - 1) / (1 + y ^ 2) ^ 2

/-- The phase variable attached to the Poisson--Cauchy profile. -/
def xiPoissonPhase (y : ℝ) : ℝ :=
  Real.arctan y

/-- The second-order profile decomposes into two low-frequency cosine channels in the phase
variable. -/
def xiPoissonPhaseTwoCosineDecomposition (y : ℝ) : Prop :=
  xiPoissonSecondOrderProfile y =
    -(Real.cos (2 * xiPoissonPhase y) + Real.cos (4 * xiPoissonPhase y)) / 2

theorem paper_xi_poisson_second_order_two_cosine_channels
    (y : ℝ) : xiPoissonPhaseTwoCosineDecomposition y := by
  unfold xiPoissonPhaseTwoCosineDecomposition xiPoissonSecondOrderProfile xiPoissonPhase
  have hy : (1 + y ^ 2 : ℝ) ≠ 0 := by nlinarith
  have hcos2 : Real.cos (2 * Real.arctan y) = (1 - y ^ 2) / (1 + y ^ 2) := by
    rw [Real.cos_two_mul']
    rw [Real.cos_sq_arctan, Real.sin_sq_arctan]
    field_simp [hy]
  have hcos4 : Real.cos (4 * Real.arctan y) = (y ^ 4 - 6 * y ^ 2 + 1) / (1 + y ^ 2) ^ 2 := by
    rw [show 4 * Real.arctan y = 2 * (2 * Real.arctan y) by ring, Real.cos_two_mul]
    rw [hcos2]
    field_simp [hy]
    ring
  rw [hcos2, hcos4]
  field_simp [hy]
  ring

end

end Omega.Zeta
