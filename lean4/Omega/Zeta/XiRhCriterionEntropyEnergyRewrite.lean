namespace Omega.Zeta

/-- Paper label: `cor:xi-rh-criterion-entropy-energy-rewrite`. -/
theorem paper_xi_rh_criterion_entropy_energy_rewrite
    (RH uniformDefect entropyEnergy : Prop) (hRH : RH ↔ uniformDefect)
    (hRewrite : uniformDefect ↔ entropyEnergy) : RH ↔ entropyEnergy := by
  exact hRH.trans hRewrite

end Omega.Zeta
