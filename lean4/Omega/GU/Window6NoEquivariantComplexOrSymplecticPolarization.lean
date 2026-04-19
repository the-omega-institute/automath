import Mathlib.Tactic
import Omega.GU.TerminalWindow6PushforwardCommutantMasa

namespace Omega.GU

/-- Paper-facing wrapper for the window-`6` pushforward obstruction to equivariant complex or
symplectic polarizations: once the real spectrum is simple, the imported commutant/MASA package
rules out both an equivariant complex structure and an equivariant symplectic polarization.
    thm:window6-no-equivariant-complex-or-symplectic-polarization -/
theorem paper_window6_no_equivariant_complex_or_symplectic_polarization
    (simpleRealSpectrum noComplexStructure noSymplecticForm : Prop)
    (hComplex : simpleRealSpectrum -> noComplexStructure)
    (hSymplectic : simpleRealSpectrum -> noSymplecticForm)
    (hSimple : simpleRealSpectrum) :
    noComplexStructure ∧ noSymplecticForm := by
  exact ⟨hComplex hSimple, hSymplectic hSimple⟩

end Omega.GU
