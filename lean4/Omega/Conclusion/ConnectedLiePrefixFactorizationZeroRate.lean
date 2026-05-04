import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter
open scoped Topology

/-- Concrete data for a connected-Lie observable that factors through a finite prefix and a finite
quotient `Q`. The information sequence is bounded by the finite quotient entropy. -/
structure conclusion_connected_lie_prefix_factorization_zero_rate_data where
  Event : Type
  Q : Type
  fintypeQ : Fintype Q
  prefixDepth : ℕ
  observable : (ℕ → Event) → Q
  information : ℕ → ℝ
  prefixFactorization :
    ∀ e e' : ℕ → Event,
      (∀ i : Fin prefixDepth, e i = e' i) → observable e = observable e'
  information_nonneg : ∀ n : ℕ, 0 ≤ information n
  information_le_finite_prefix : ∀ n : ℕ, information n ≤ Real.log (Fintype.card Q)

attribute [instance] conclusion_connected_lie_prefix_factorization_zero_rate_data.fintypeQ

namespace conclusion_connected_lie_prefix_factorization_zero_rate_data

/-- The observable is finite-prefix measurable and its per-symbol information rate tends to zero. -/
def zeroInformationRate
    (D : conclusion_connected_lie_prefix_factorization_zero_rate_data) : Prop :=
  (∀ e e' : ℕ → D.Event,
      (∀ i : Fin D.prefixDepth, e i = e' i) → D.observable e = D.observable e') ∧
    (∀ n : ℕ, D.information n ≤ Real.log (Fintype.card D.Q)) ∧
      Tendsto (fun n : ℕ => D.information n / (n : ℝ)) atTop (𝓝 0)

end conclusion_connected_lie_prefix_factorization_zero_rate_data

/-- Paper label: `thm:conclusion-connected-lie-prefix-factorization-zero-rate`. -/
theorem paper_conclusion_connected_lie_prefix_factorization_zero_rate
    (D : conclusion_connected_lie_prefix_factorization_zero_rate_data) :
    D.zeroInformationRate := by
  refine ⟨D.prefixFactorization, D.information_le_finite_prefix, ?_⟩
  have hbound_tendsto :
      Tendsto (fun n : ℕ => Real.log (Fintype.card D.Q) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound_tendsto ?_ ?_
  · intro n
    exact div_nonneg (D.information_nonneg n) (by
      show (0 : ℝ) ≤ (n : ℝ)
      exact_mod_cast Nat.zero_le n)
  · intro n
    exact div_le_div_of_nonneg_right (D.information_le_finite_prefix n)
      (by
        show (0 : ℝ) ≤ (n : ℝ)
        exact_mod_cast Nat.zero_le n)

end Omega.Conclusion
