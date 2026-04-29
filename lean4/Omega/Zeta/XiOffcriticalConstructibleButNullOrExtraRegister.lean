namespace Omega.Zeta

theorem paper_xi_offcritical_constructible_but_null_or_extra_register
    (selfDual offlineZero radialChannel nullReadout extraRegister noThirdPath : Prop)
    (hself : selfDual) (hoff : offlineZero → radialChannel)
    (hnull : radialChannel → nullReadout) (hextra : radialChannel → extraRegister)
    (hno : noThirdPath) :
    selfDual ∧ (offlineZero → radialChannel) ∧ (radialChannel → nullReadout) ∧
      (radialChannel → extraRegister) ∧ noThirdPath := by
  exact ⟨hself, hoff, hnull, hextra, hno⟩

end Omega.Zeta
