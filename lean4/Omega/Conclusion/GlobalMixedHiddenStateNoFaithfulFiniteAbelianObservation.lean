import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-global-mixed-hidden-state-no-faithful-finite-abelian-observation`. -/
theorem paper_conclusion_global_mixed_hidden_state_no_faithful_finite_abelian_observation
    {H G : Type} [Infinite H] [Fintype G] (φ : H → G) :
    ¬ Function.Injective φ := by
  exact not_injective_infinite_finite φ

end Omega.Conclusion
