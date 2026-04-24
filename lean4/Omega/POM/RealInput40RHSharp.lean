import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.RealInput40ZetaFactorization

namespace Omega.POM

open scoped goldenRatio

/-- Paper label: `thm:pom-rh-sharp`.
On the explicit non-Perron root list coming from the real-input `40` determinant factorization,
every absolute value is at most `φ`, and equality occurs only at the negative golden-ratio root.
-/
theorem paper_pom_rh_sharp :
    (∀ ν : ℝ,
      (ν = -Real.goldenRatio ∨ ν = 1 ∨ ν = -1 ∨
        ν = 1 / Real.goldenRatio ∨ ν = -(1 / Real.goldenRatio)) →
        |ν| ≤ Real.goldenRatio) ∧
    (∀ ν : ℝ,
      (ν = -Real.goldenRatio ∨ ν = 1 ∨ ν = -1 ∨
        ν = 1 / Real.goldenRatio ∨ ν = -(1 / Real.goldenRatio)) →
        |ν| = Real.goldenRatio → ν = -Real.goldenRatio) := by
  have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hInvLeOne : 1 / Real.goldenRatio ≤ (1 : ℝ) := by
    exact (div_le_one hphi_pos).2 (le_of_lt Real.one_lt_goldenRatio)
  have hInvLe : 1 / Real.goldenRatio ≤ Real.goldenRatio := by
    exact le_trans hInvLeOne (le_of_lt Real.one_lt_goldenRatio)
  have hInvLt : 1 / Real.goldenRatio < Real.goldenRatio := by
    exact lt_trans ((div_lt_one hphi_pos).2 Real.one_lt_goldenRatio) Real.one_lt_goldenRatio
  refine ⟨?_, ?_⟩
  · intro ν hν
    rcases hν with rfl | rfl | rfl | rfl | rfl
    · rw [abs_neg, abs_of_nonneg (le_of_lt hphi_pos)]
    · norm_num
      exact le_of_lt Real.one_lt_goldenRatio
    · rw [abs_neg]
      norm_num
      exact le_of_lt Real.one_lt_goldenRatio
    · rw [abs_of_nonneg (by positivity : 0 ≤ (1 / Real.goldenRatio : ℝ))]
      exact hInvLe
    · rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (1 / Real.goldenRatio : ℝ))]
      exact hInvLe
  · intro ν hν hEq
    rcases hν with rfl | rfl | rfl | rfl | rfl
    · rfl
    · norm_num at hEq
      have : (1 : ℝ) = Real.goldenRatio := hEq
      linarith [Real.one_lt_goldenRatio]
    · rw [abs_neg] at hEq
      norm_num at hEq
      have : (1 : ℝ) = Real.goldenRatio := hEq
      linarith [Real.one_lt_goldenRatio]
    · rw [abs_of_nonneg (by positivity : 0 ≤ (1 / Real.goldenRatio : ℝ))] at hEq
      have : (1 / Real.goldenRatio : ℝ) = Real.goldenRatio := hEq
      linarith
    · rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (1 / Real.goldenRatio : ℝ))] at hEq
      have : (1 / Real.goldenRatio : ℝ) = Real.goldenRatio := hEq
      linarith

end Omega.POM
