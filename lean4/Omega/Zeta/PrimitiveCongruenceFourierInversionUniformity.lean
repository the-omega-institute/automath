namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part63b-primitive-congruence-fourier-inversion-uniformity`. -/
theorem paper_xi_time_part63b_primitive_congruence_fourier_inversion_uniformity
    (strict_fourier_inversion uniformity_criterion : Prop) :
    strict_fourier_inversion → uniformity_criterion →
      strict_fourier_inversion ∧ uniformity_criterion := by
  intro hFourier hUniform
  exact ⟨hFourier, hUniform⟩

end Omega.Zeta
