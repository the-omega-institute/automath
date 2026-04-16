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

end Omega.Zeta
