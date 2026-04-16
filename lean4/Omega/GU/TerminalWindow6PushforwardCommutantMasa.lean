namespace Omega.GU

/-- Paper-facing wrapper for the window-`6` pushforward commutant being a polynomial masa.
    thm:terminal-window6-pushforward-commutant-masa -/
theorem paper_terminal_window6_pushforward_commutant_masa
    (simpleSpectrum commutantIsPolynomial commutantIsC21 unitaryIsTorus21 masa : Prop)
    (hPoly : simpleSpectrum -> commutantIsPolynomial)
    (hC21 : commutantIsPolynomial -> commutantIsC21)
    (hTorus : commutantIsC21 -> unitaryIsTorus21)
    (hMasa : simpleSpectrum -> masa)
    (hSimple : simpleSpectrum) :
    commutantIsPolynomial ∧ commutantIsC21 ∧ unitaryIsTorus21 ∧ masa := by
  have hPolynomial : commutantIsPolynomial := hPoly hSimple
  have hC21' : commutantIsC21 := hC21 hPolynomial
  exact ⟨hPolynomial, hC21', hTorus hC21', hMasa hSimple⟩

end Omega.GU
