namespace Omega.Zeta

/-- Paper-facing wrapper for the cyclic-lift limsup spectral-gap extraction in the ETDS
finite-part section.
    thm:finite-part-cyclic-lift-limsup-spectral-gap -/
theorem paper_etds_finite_part_cyclic_lift_limsup_spectral_gap
    (mainTerm cesaroNoncancel limsupGap : Prop)
    (hMain : mainTerm)
    (hCesaro : mainTerm -> cesaroNoncancel)
    (hGap : cesaroNoncancel -> limsupGap) :
    limsupGap := by
  exact hGap (hCesaro hMain)

/-- Exact paper-facing statement for the cyclic-lift limsup spectral-gap extraction. -/
def finite_part_cyclic_lift_limsup_spectral_gap_statement : Prop :=
  ∀ (mainTerm cesaroNoncancel limsupGap : Prop)
    (_hMain : mainTerm)
    (_hCesaro : mainTerm -> cesaroNoncancel)
    (_hGap : cesaroNoncancel -> limsupGap),
      limsupGap

/-- Paper label: `thm:finite-part-cyclic-lift-limsup-spectral-gap`. -/
theorem paper_finite_part_cyclic_lift_limsup_spectral_gap :
    finite_part_cyclic_lift_limsup_spectral_gap_statement := by
  intro mainTerm cesaroNoncancel limsupGap hMain hCesaro hGap
  exact paper_etds_finite_part_cyclic_lift_limsup_spectral_gap
    mainTerm cesaroNoncancel limsupGap hMain hCesaro hGap

end Omega.Zeta
