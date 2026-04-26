import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Folding.TranslationKernelFourierSgM

namespace Omega.Zeta

/-- The requested `paper_xi_time_part72a_zero_coset_global_inclusion_odd_divisibility` signature
omits the paper's evenness hypothesis on `M`; under the current `sgMFrequencySet` definition, its
specialization at `M = 0`, `g = 1`, and `h = 2` is false. -/
theorem xi_time_part72a_zero_coset_global_inclusion_odd_divisibility_requested_statement_false :
    ¬ ((Omega.Folding.sgMFrequencySet 0 1 ⊆ Omega.Folding.sgMFrequencySet 0 2) ↔
        1 ∣ 2 ∧ Odd (2 / 1)) := by
  intro hiff
  have hIncl : Omega.Folding.sgMFrequencySet 0 1 ⊆ Omega.Folding.sgMFrequencySet 0 2 := by
    have h1 : Omega.Folding.sgMFrequencySet 0 1 = ({0} : Finset ℕ) := by
      native_decide
    have h2 : Omega.Folding.sgMFrequencySet 0 2 = ({0} : Finset ℕ) := by
      native_decide
    intro x hx
    rw [h1] at hx
    rw [h2]
    simpa using hx
  have hOdd : 1 ∣ 2 ∧ Odd (2 / 1) := hiff.mp hIncl
  exact (by decide : ¬ Odd 2) (by simpa using hOdd.2)

end Omega.Zeta
