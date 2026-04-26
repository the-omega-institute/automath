namespace Omega.Zeta

/-- Paper label: `thm:xi-endpoint-absorption-inversion-uniqueness`. -/
theorem paper_xi_endpoint_absorption_inversion_uniqueness
    (finiteDefect rationalEndpointProfile poleSetDeterminesCayleyZeros
      intervalEqualityDeterminesZeros : Prop)
    (hRat : finiteDefect -> rationalEndpointProfile)
    (hPole : rationalEndpointProfile -> poleSetDeterminesCayleyZeros)
    (hUniq : poleSetDeterminesCayleyZeros -> intervalEqualityDeterminesZeros)
    (hFinite : finiteDefect) :
    rationalEndpointProfile ∧ intervalEqualityDeterminesZeros := by
  have hRational : rationalEndpointProfile := hRat hFinite
  exact ⟨hRational, hUniq (hPole hRational)⟩

end Omega.Zeta
