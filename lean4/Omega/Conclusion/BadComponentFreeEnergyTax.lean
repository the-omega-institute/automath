import Omega.Conclusion.FixedBadComponentLayerSharpMainTerm

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-bad-component-free-energy-tax`. -/
theorem paper_conclusion_bad_component_free_energy_tax
    (D : conclusion_fixed_bad_component_layer_sharp_main_term_data) (Gamma : ℚ)
    (taxAsymptotic : Prop) (hGamma_pos : 0 < Gamma) (hTax : taxAsymptotic) :
    0 < Gamma ∧
      D.conclusion_fixed_bad_component_layer_sharp_main_term_sharp_asymptotic ∧
      taxAsymptotic := by
  exact ⟨hGamma_pos, (paper_conclusion_fixed_bad_component_layer_sharp_main_term D).2, hTax⟩

end Omega.Conclusion
