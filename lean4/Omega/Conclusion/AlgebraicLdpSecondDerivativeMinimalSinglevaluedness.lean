import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-algebraic-ldp-second-derivative-minimal-singlevaluedness`. -/
theorem paper_conclusion_algebraic_ldp_second_derivative_minimal_singlevaluedness
    {Γ : Type*} [Group Γ] (k : Γ → ℤ)
    (firstDerivativeSingleValued secondDerivativeSingleValued : Prop)
    (hsecond : secondDerivativeSingleValued)
    (hfirst : firstDerivativeSingleValued ↔ ∀ γ, k γ = 0)
    (hnonzero : ∃ γ, k γ ≠ 0) :
    secondDerivativeSingleValued ∧ ¬ firstDerivativeSingleValued := by
  constructor
  · exact hsecond
  · intro hsingle
    rcases hnonzero with ⟨γ, hγ⟩
    exact hγ ((hfirst.mp hsingle) γ)

/-- Paper label: `cor:conclusion-algebraic-ldp-minimal-covering-kernel-k`. -/
theorem paper_conclusion_algebraic_ldp_minimal_covering_kernel_k {Γ : Type*} [Group Γ]
    (k : Γ → ℤ) (singleValuedOnKernel minimalCover residualConstantTranslation : Prop)
    (hSingle : singleValuedOnKernel) (hMinimal : minimalCover)
    (hResidual : residualConstantTranslation) :
    singleValuedOnKernel ∧ minimalCover ∧ residualConstantTranslation := by
  have _ : Nonempty (Γ → ℤ) := ⟨k⟩
  exact ⟨hSingle, hMinimal, hResidual⟩

end Omega.Conclusion
