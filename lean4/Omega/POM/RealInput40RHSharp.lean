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

/-- The explicit trace model obtained by summing the powers of the audited real-input `40`
nonzero roots. -/
noncomputable def pom_rh_sharp_an_trace (n : ℕ) : ℝ :=
  Real.goldenRatio ^ (2 * n) + (-Real.goldenRatio) ^ n + 1 + (-1 : ℝ) ^ n +
    (1 / Real.goldenRatio) ^ n + (-(1 / Real.goldenRatio)) ^ n

/-- The error after removing the Perron contribution `φ^(2n)`. -/
noncomputable def pom_rh_sharp_an_error (n : ℕ) : ℝ :=
  pom_rh_sharp_an_trace n - Real.goldenRatio ^ (2 * n)

/-- Paper label: `cor:pom-rh-sharp-an`.
For the explicit real-input `40` trace model, the non-oscillating remainder after removing
`φ^(2n)` and `(-φ)^n` is uniformly bounded, while the odd subsequence still contains the exact
`-φ^n` oscillation. -/
theorem paper_pom_rh_sharp_an :
    (∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, |pom_rh_sharp_an_error n - (-Real.goldenRatio) ^ n| ≤ C) ∧
    (∀ n : ℕ, pom_rh_sharp_an_error (2 * n + 1) = -Real.goldenRatio ^ (2 * n + 1)) := by
  have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hinv_nonneg : 0 ≤ (1 / Real.goldenRatio : ℝ) := by positivity
  have hinv_le_one : (1 / Real.goldenRatio : ℝ) ≤ 1 := by
    exact (div_le_one hphi_pos).2 (le_of_lt Real.one_lt_goldenRatio)
  refine ⟨⟨4, by norm_num, ?_⟩, ?_⟩
  · intro n
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    ·
      have hpow_le_one : (1 / Real.goldenRatio : ℝ) ^ (2 * k) ≤ 1 := by
        exact pow_le_one₀ hinv_nonneg hinv_le_one
      have hpow_nonneg : 0 ≤ (1 / Real.goldenRatio : ℝ) ^ (2 * k) := by
        exact pow_nonneg hinv_nonneg _
      have hcalc :
          pom_rh_sharp_an_error (2 * k) - (-Real.goldenRatio) ^ (2 * k) =
            2 + 2 * (1 / Real.goldenRatio : ℝ) ^ (2 * k) := by
        norm_num [pom_rh_sharp_an_error, pom_rh_sharp_an_trace, pow_add, pow_mul]
        nlinarith
      have hbound : |2 + 2 * (1 / Real.goldenRatio : ℝ) ^ (2 * k)| ≤ 4 := by
        rw [abs_of_nonneg]
        · nlinarith
        · nlinarith
      have hkk : k + k = 2 * k := by omega
      rw [hkk]
      rw [hcalc]
      exact hbound
    ·
      norm_num [pom_rh_sharp_an_error, pom_rh_sharp_an_trace, pow_add, pow_mul]
  · intro n
    norm_num [pom_rh_sharp_an_error, pom_rh_sharp_an_trace, pow_add, pow_mul]

end Omega.POM
