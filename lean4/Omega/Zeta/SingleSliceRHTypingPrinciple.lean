namespace Omega.Zeta

/-- Paper label: `cor:xi-single-slice-rh-typing-principle`. -/
theorem paper_xi_single_slice_rh_typing_principle
    (protocolInvariant readReflects blaschkeZero jensenHorizon rhDecoded : Prop)
    (hReflect : protocolInvariant → readReflects)
    (hBlaschke : readReflects → blaschkeZero)
    (hJensen : blaschkeZero → jensenHorizon) (hRH : jensenHorizon → rhDecoded) :
    protocolInvariant → rhDecoded := by
  intro hProtocol
  exact hRH (hJensen (hBlaschke (hReflect hProtocol)))

end Omega.Zeta
