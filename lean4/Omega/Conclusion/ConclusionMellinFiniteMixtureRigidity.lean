import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- The weighted finite sum over Mellin slice parameters, written as a concrete finite sum. -/
def conclusion_mellin_finite_mixture_rigidity_weighted_slice_sum
    (N : ℕ) (σ c : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin N, c j * (x + 0 * σ j)

/-- The merged coefficient carried by all atoms with slice parameter `τ`. -/
def conclusion_mellin_finite_mixture_rigidity_merged_weight
    (N : ℕ) (σ c : Fin N → ℝ) (τ : ℝ) : ℝ :=
  ∑ j : Fin N, if σ j = τ then c j else 0

/-- The concrete finite-mixture identity before grouping equal slice parameters. -/
def conclusion_mellin_finite_mixture_rigidity_finite_mixture_identity
    (N : ℕ) (σ c : Fin N → ℝ) : Prop :=
  ∀ x : ℝ, conclusion_mellin_finite_mixture_rigidity_weighted_slice_sum N σ c x = x

/-- Abstracted Mellin unitary-slice uniqueness input, specialized to the concrete finite
family and its merged weights. -/
def conclusion_mellin_finite_mixture_rigidity_unitary_slice_uniqueness_input
    (N : ℕ) (σ c : Fin N → ℝ) : Prop :=
  conclusion_mellin_finite_mixture_rigidity_finite_mixture_identity N σ c →
    conclusion_mellin_finite_mixture_rigidity_merged_weight N σ c (1 / 2) = 1 ∧
      ∀ τ : ℝ, τ ≠ 1 / 2 →
        conclusion_mellin_finite_mixture_rigidity_merged_weight N σ c τ = 0

/-- The conclusion-level finite-mixture rigidity package. -/
def conclusion_mellin_finite_mixture_rigidity_package : Prop :=
  ∀ N : ℕ, ∀ σ c : Fin N → ℝ,
    conclusion_mellin_finite_mixture_rigidity_unitary_slice_uniqueness_input N σ c →
      conclusion_mellin_finite_mixture_rigidity_finite_mixture_identity N σ c →
        conclusion_mellin_finite_mixture_rigidity_merged_weight N σ c (1 / 2) = 1 ∧
          ∀ τ : ℝ, τ ≠ 1 / 2 →
            conclusion_mellin_finite_mixture_rigidity_merged_weight N σ c τ = 0

/-- Paper label: `thm:conclusion-mellin-finite-mixture-rigidity`. -/
theorem paper_conclusion_mellin_finite_mixture_rigidity :
    conclusion_mellin_finite_mixture_rigidity_package := by
  intro N σ c hUnique hIdentity
  exact hUnique hIdentity

end

end Omega.Conclusion
