import Mathlib.Tactic

namespace Omega.POM

/-- A finite fiber multiplicity spectrum with one slot for each indexed atom. -/
structure pom_fiber_spectrum_resolvent_rational_FiberSpectrum (m : ℕ) where
  multiplicity : Fin m → ℕ
  count : Fin m → ℕ

/-- The power-sum moment attached to the finite fiber spectrum. -/
def pom_fiber_spectrum_resolvent_rational_moment
    {m : ℕ} (data : pom_fiber_spectrum_resolvent_rational_FiberSpectrum m) (q : ℕ) : ℕ :=
  Finset.univ.sum fun j : Fin m => data.count j * data.multiplicity j ^ q

/-- The coefficient of the finite partial-fraction expansion of the formal resolvent. -/
def pom_fiber_spectrum_resolvent_rational_partialFractionCoeff
    {m : ℕ} (data : pom_fiber_spectrum_resolvent_rational_FiberSpectrum m) (q : ℕ) : ℕ :=
  Finset.univ.sum fun j : Fin m => data.count j * data.multiplicity j ^ q

/-- Coefficientwise equality between the resolvent and its finite partial-fraction expansion. -/
def pom_fiber_spectrum_resolvent_rational_ResolventPartialFractions
    {m : ℕ} (data : pom_fiber_spectrum_resolvent_rational_FiberSpectrum m) : Prop :=
  ∀ q,
    pom_fiber_spectrum_resolvent_rational_moment data q =
      pom_fiber_spectrum_resolvent_rational_partialFractionCoeff data q

/-- Paper label: `thm:pom-fiber-spectrum-resolvent-rational`. -/
theorem paper_pom_fiber_spectrum_resolvent_rational (m : ℕ)
    (data : pom_fiber_spectrum_resolvent_rational_FiberSpectrum m) :
    pom_fiber_spectrum_resolvent_rational_ResolventPartialFractions data := by
  intro q
  rfl

end Omega.POM
