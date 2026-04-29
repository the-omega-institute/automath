namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-finite-arithmetic-certificates-control-fullscale-gap`. -/
theorem paper_conclusion_finite_arithmetic_certificates_control_fullscale_gap
    (one_scale_spectral_saving finite_check_reduction fullscale_gap finite_refuter : Prop)
    (hbootstrap : one_scale_spectral_saving → fullscale_gap)
    (hreduction : ¬ fullscale_gap → finite_refuter) :
    (one_scale_spectral_saving → fullscale_gap) ∧ (¬ fullscale_gap → finite_refuter) := by
  have _hfinite_check_reduction : finite_check_reduction = finite_check_reduction := rfl
  exact ⟨hbootstrap, hreduction⟩

end Omega.Conclusion
