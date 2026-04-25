import Mathlib.Tactic
import Omega.Conclusion.ConnectedToDiscreteConstant

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-screenphase-connected-quotient-no-binary-anomaly-register`. -/
theorem paper_conclusion_screenphase_connected_quotient_no_binary_anomaly_register
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ConnectedSpace X]
    [DiscreteTopology Y] [Nontrivial Y] :
    ¬ ∃ f : X → Y, Continuous f ∧ Function.Surjective f := by
  rintro ⟨f, hf, hsurj⟩
  have hconst : ∀ x y : X, f x = f y :=
    Omega.Conclusion.ConnectedToDiscreteConstant.continuous_to_discrete_constant f hf
  obtain ⟨y₀, y₁, hy⟩ := exists_pair_ne Y
  obtain ⟨x₀, hx₀⟩ := hsurj y₀
  obtain ⟨x₁, hx₁⟩ := hsurj y₁
  have : y₀ = y₁ := by
    calc
      y₀ = f x₀ := hx₀.symm
      _ = f x₁ := hconst x₀ x₁
      _ = y₁ := hx₁
  exact hy this

end Omega.Conclusion
