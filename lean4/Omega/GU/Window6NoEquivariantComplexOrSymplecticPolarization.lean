import Mathlib.Tactic

namespace Omega.GU

/-- Paper-facing wrapper for the window-`6` pushforward obstruction to equivariant complex or
symplectic polarizations.
    thm:window6-no-equivariant-complex-or-symplectic-polarization -/
theorem paper_window6_no_equivariant_complex_or_symplectic_polarization
    (simpleSpectrum noComplexStructure noSymplecticForm : Prop)
    (hComplex : simpleSpectrum -> noComplexStructure)
    (hSymplectic : simpleSpectrum -> noSymplecticForm)
    (hSimple : simpleSpectrum) : noComplexStructure ∧ noSymplecticForm := by
  exact ⟨hComplex hSimple, hSymplectic hSimple⟩

end Omega.GU
