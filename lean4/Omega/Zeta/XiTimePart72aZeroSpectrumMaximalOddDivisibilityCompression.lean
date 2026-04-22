import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Folding.TranslationKernelFourierSgM

namespace Omega.Zeta

open scoped BigOperators

/-- The requested `paper_xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression`
signature inherits the same missing evenness hypothesis on `M`; under the current
`sgMFrequencySet` definition, its specialization at `M = 0` and `G = {1, 2}` is false. -/
theorem
    xi_time_part72a_zero_spectrum_maximal_odd_divisibility_compression_requested_statement_false :
    ¬ (let G : Finset ℕ := {1, 2}
       let maximal := G.filter (fun g => ∀ h ∈ G, g ∣ h → Odd (h / g) → h = g)
       (⋃ g ∈ G, (↑(Omega.Folding.sgMFrequencySet 0 g) : Set ℕ)) =
         ⋃ g ∈ maximal, (↑(Omega.Folding.sgMFrequencySet 0 g) : Set ℕ) ∧
       ∀ A : Finset ℕ, A ⊆ G →
         (⋃ g ∈ G, (↑(Omega.Folding.sgMFrequencySet 0 g) : Set ℕ)) =
           ⋃ g ∈ A, (↑(Omega.Folding.sgMFrequencySet 0 g) : Set ℕ) →
         maximal ⊆ A) := by
  dsimp
  intro h
  have hsubset : ({1} : Finset ℕ) ⊆ ({1, 2} : Finset ℕ) := by
    simp
  have h1 : Omega.Folding.sgMFrequencySet 0 1 = ({0} : Finset ℕ) := by
    native_decide
  have h2 : Omega.Folding.sgMFrequencySet 0 2 = ({0} : Finset ℕ) := by
    native_decide
  have hUnionG :
      (⋃ g ∈ ({1, 2} : Finset ℕ), (↑(Omega.Folding.sgMFrequencySet 0 g) : Set ℕ)) =
        ({0} : Set ℕ) := by
    ext x
    simp [h1, h2]
  have hUnionA :
      (⋃ g ∈ ({1} : Finset ℕ), (↑(Omega.Folding.sgMFrequencySet 0 g) : Set ℕ)) =
        ({0} : Set ℕ) := by
    ext x
    simp [h1]
  have hMin := h.2 ({1} : Finset ℕ) hsubset (hUnionG.trans hUnionA.symm)
  have hTwoIn :
      2 ∈ ({g ∈ ({1, 2} : Finset ℕ) | ∀ h ∈ ({1, 2} : Finset ℕ), g ∣ h → Odd (h / g) → h = g}) := by
    simp
  have hTwoMem : 2 ∈ ({1} : Finset ℕ) := hMin hTwoIn
  simp at hTwoMem

end Omega.Zeta
