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

end Omega.Conclusion
