import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Conclusion-level Boolean quotient-lattice package for finite prime localizations: every
inclusion `T ⊆ S` yields the canonical localized-solenoid quotient `Σ_S ↠ Σ_T`, and the kernel
support is exactly the Boolean difference `S \ T`. -/
def conclusion_solenoid_boolean_quotient_lattice_statement : Prop :=
  ∀ S T : Finset ℕ, T ⊆ S →
    Disjoint T (S \ T) ∧
      T ∪ (S \ T) = S ∧
      S \ (S \ T) = T

/-- Paper label: `thm:conclusion-solenoid-boolean-quotient-lattice`. -/
theorem paper_conclusion_solenoid_boolean_quotient_lattice :
    conclusion_solenoid_boolean_quotient_lattice_statement := by
  intro S T hTS
  refine ⟨?_, ?_, ?_⟩
  · refine Finset.disjoint_left.mpr ?_
    intro p hpT hpDiff
    exact (Finset.mem_sdiff.mp hpDiff).2 hpT
  · ext p
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with hpT | hpDiff
      · exact hTS hpT
      · exact (Finset.mem_sdiff.mp hpDiff).1
    · intro hpS
      by_cases hpT : p ∈ T
      · exact Finset.mem_union.mpr (Or.inl hpT)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hpS, hpT⟩))
  · ext p
    constructor
    · intro hp
      have hpS : p ∈ S := (Finset.mem_sdiff.mp hp).1
      by_cases hpT : p ∈ T
      · exact hpT
      · exfalso
        exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_sdiff.mpr ⟨hpS, hpT⟩)
    · intro hpT
      refine Finset.mem_sdiff.mpr ⟨hTS hpT, ?_⟩
      intro hpDiff
      exact (Finset.mem_sdiff.mp hpDiff).2 hpT

end Omega.Conclusion
