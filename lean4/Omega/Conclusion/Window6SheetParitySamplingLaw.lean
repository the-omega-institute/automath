import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Boolean sheet-parity bit written in the paper's `±1` convention. -/
def conclusion_window6_sheet_parity_sampling_law_sign (b : Bool) : ℝ :=
  if b then 1 else -1

/-- Empirical average of the sampled sheet-parity signs. -/
noncomputable def conclusion_window6_sheet_parity_sampling_law_empirical_mean {n : ℕ}
    (X : Fin n → Bool) : ℝ :=
  (∑ j, conclusion_window6_sheet_parity_sampling_law_sign (X j)) / n

/-- Hoeffding-scale tail for a single `±1` coordinate. -/
noncomputable def conclusion_window6_sheet_parity_sampling_law_hoeffding_tail
    (n : ℕ) (η : ℝ) : ℝ :=
  2 * Real.exp (-(2 : ℝ) * (n : ℝ) * η ^ 2)

/-- Paper label: `thm:conclusion-window6-sheet-parity-sampling-law`. If the two sheet-parity
coordinates have means at least `1 - ε`, the empirical averages stay within `η` of those means,
and each Hoeffding tail is bounded by the usual one-coordinate estimate, then both empirical
coordinates stay above `1 - ε - η` and the joint failure probability is controlled by the union
bound. -/
theorem paper_conclusion_window6_sheet_parity_sampling_law
    {n : ℕ} (ε η p₁ p₂ μ₁ μ₂ : ℝ) (X₁ X₂ : Fin n → Bool)
    (hμ₁ : 1 - ε ≤ μ₁) (hμ₂ : 1 - ε ≤ μ₂)
    (hdev₁ :
      |conclusion_window6_sheet_parity_sampling_law_empirical_mean X₁ - μ₁| ≤ η)
    (hdev₂ :
      |conclusion_window6_sheet_parity_sampling_law_empirical_mean X₂ - μ₂| ≤ η)
    (hp₁ : p₁ ≤ conclusion_window6_sheet_parity_sampling_law_hoeffding_tail n η)
    (hp₂ : p₂ ≤ conclusion_window6_sheet_parity_sampling_law_hoeffding_tail n η) :
    1 - ε - η ≤ conclusion_window6_sheet_parity_sampling_law_empirical_mean X₁ ∧
      1 - ε - η ≤ conclusion_window6_sheet_parity_sampling_law_empirical_mean X₂ ∧
      p₁ + p₂ ≤ 2 * conclusion_window6_sheet_parity_sampling_law_hoeffding_tail n η := by
  have hdev₁_left :
      -η ≤ conclusion_window6_sheet_parity_sampling_law_empirical_mean X₁ - μ₁ :=
    (abs_le.mp hdev₁).1
  have hdev₂_left :
      -η ≤ conclusion_window6_sheet_parity_sampling_law_empirical_mean X₂ - μ₂ :=
    (abs_le.mp hdev₂).1
  have hmean₁ :
      1 - ε - η ≤ conclusion_window6_sheet_parity_sampling_law_empirical_mean X₁ := by
    linarith
  have hmean₂ :
      1 - ε - η ≤ conclusion_window6_sheet_parity_sampling_law_empirical_mean X₂ := by
    linarith
  have hprob :
      p₁ + p₂ ≤ 2 * conclusion_window6_sheet_parity_sampling_law_hoeffding_tail n η := by
    linarith
  exact ⟨hmean₁, hmean₂, hprob⟩

end Omega.Conclusion
