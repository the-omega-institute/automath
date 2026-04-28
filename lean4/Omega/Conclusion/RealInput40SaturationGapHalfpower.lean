import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-saturation-gap-halfpower`. -/
theorem conclusion_realinput40_saturation_gap_halfpower_propositional_chain
    (puiseux_pressure_expansion theta_gap_law u_gap_law leading_constant_positive : Prop)
    (hθ : puiseux_pressure_expansion → theta_gap_law)
    (hu : theta_gap_law → u_gap_law)
    (hc : puiseux_pressure_expansion → leading_constant_positive)
    (hP : puiseux_pressure_expansion) :
    theta_gap_law ∧ u_gap_law ∧ leading_constant_positive := by
  exact ⟨hθ hP, hu (hθ hP), hc hP⟩

end Omega.Conclusion
