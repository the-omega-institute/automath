import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- The single numerical spectral decision: a uniform positive gap below the benchmark
`1 / (M + 1)` for all rational-frequency Gram scales. -/
def gm_unified_reduction_one_spectral_number_decision (gramRadius : ℕ → ℝ) : Prop :=
  ∃ theta : ℝ, 0 < theta ∧
    ∀ M : ℕ, gramRadius M + theta ≤ 1 / ((M : ℝ) + 1)

/-- The analytic branch: the chosen large-value bound has a uniform saving. -/
def gm_unified_reduction_one_spectral_number_uniform_saving
    (largeValueBound : ℕ → ℝ) : Prop :=
  ∃ theta : ℝ, 0 < theta ∧ ∀ M : ℕ, largeValueBound M ≤ 1 - theta

/-- The obstruction branch: every requested gap is violated at some scale and is witnessed by
a nonnegative resonance score. -/
def gm_unified_reduction_one_spectral_number_arithmetic_obstruction
    (gramRadius resonanceScore : ℕ → ℝ) : Prop :=
  ∀ theta : ℝ, 0 < theta →
    ∃ M : ℕ, 1 / ((M : ℝ) + 1) < gramRadius M + theta ∧ 0 ≤ resonanceScore M

/-- Paper label: `thm:gm-unified-reduction-one-spectral-number`. -/
theorem paper_gm_unified_reduction_one_spectral_number
    (gramRadius largeValueBound resonanceScore : ℕ → ℝ)
    (hSaving :
      gm_unified_reduction_one_spectral_number_decision gramRadius →
        gm_unified_reduction_one_spectral_number_uniform_saving largeValueBound)
    (hObstruction :
      ¬ gm_unified_reduction_one_spectral_number_decision gramRadius →
        gm_unified_reduction_one_spectral_number_arithmetic_obstruction
          gramRadius resonanceScore) :
    (gm_unified_reduction_one_spectral_number_decision gramRadius ∧
        gm_unified_reduction_one_spectral_number_uniform_saving largeValueBound) ∨
      (¬ gm_unified_reduction_one_spectral_number_decision gramRadius ∧
        gm_unified_reduction_one_spectral_number_arithmetic_obstruction
          gramRadius resonanceScore) := by
  classical
  by_cases hDecision : gm_unified_reduction_one_spectral_number_decision gramRadius
  · exact Or.inl ⟨hDecision, hSaving hDecision⟩
  · exact Or.inr ⟨hDecision, hObstruction hDecision⟩

end Omega.SyncKernelRealInput
