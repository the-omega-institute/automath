import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm

namespace Omega.Zeta

/-- Paper label: `prop:xi-leyang-two-hypothesis-unit-circle`. -/
theorem paper_xi_leyang_two_hypothesis_unit_circle (n : ℕ) (hn : n ≠ 0) :
    ∀ z : ℂ, z ^ n + 1 = 0 -> ‖z‖ = 1 := by
  intro z hz
  have hzpow : z ^ n = (-1 : ℂ) := eq_neg_of_add_eq_zero_left hz
  have hnormpow : ‖z‖ ^ n = 1 := by
    calc
      ‖z‖ ^ n = ‖z ^ n‖ := by rw [norm_pow]
      _ = ‖(-1 : ℂ)‖ := by rw [hzpow]
      _ = 1 := by simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn).mp hnormpow

end Omega.Zeta
