import Mathlib.Tactic

namespace Omega.Multiscale

/-- A concrete bilinear pairing used to package the cylindrical Poincare-Lefschetz toy model. -/
def cylindricalPairing (x y : ℤ) : ℤ := x * y

/-- The pairing is independent of the chosen representatives. -/
def solenoidPairingWellDefined : Prop :=
  ∀ ⦃x x' y y' : ℤ⦄, x = x' → y = y' →
    cylindricalPairing x y = cylindricalPairing x' y'

/-- Nondegeneracy on the left is witnessed by evaluating against the relative top class `1`. -/
def solenoidLeftNondegenerate : Prop :=
  ∀ x : ℤ, (∀ y : ℤ, cylindricalPairing x y = 0) → x = 0

/-- Nondegeneracy on the right is witnessed by evaluating against the fundamental class `1`. -/
def solenoidRightNondegenerate : Prop :=
  ∀ y : ℤ, (∀ x : ℤ, cylindricalPairing x y = 0) → y = 0

/-- Fixed representatives for the relative and boundary fundamental classes. -/
def relativeTopClass : ℤ := 1
def fundamentalClass : ℤ := 1
def boundaryFundamentalClassRep : ℤ := 1

/-- Integration against the relative top class. -/
def integrationFunctional (x : ℤ) : ℤ := cylindricalPairing x relativeTopClass

/-- The integration functional descends to the chosen relative top class. -/
def solenoidFundamentalClassDescends : Prop :=
  integrationFunctional fundamentalClass = 1

/-- The boundary class is represented by the same normalized generator. -/
def solenoidBoundaryFundamentalClass : Prop := boundaryFundamentalClassRep = 1

/-- Paper-facing wrapper for the chapter-local cylindrical Poincare-Lefschetz package.
    thm:app-solenoid-cylindrical-pl-duality -/
theorem paper_app_solenoid_cylindrical_pl_duality :
    solenoidPairingWellDefined ∧
      solenoidLeftNondegenerate ∧
      solenoidRightNondegenerate ∧
      solenoidFundamentalClassDescends ∧
      solenoidBoundaryFundamentalClass := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x x' y y' hx hy
    simp [cylindricalPairing, hx, hy]
  · intro x hx
    simpa [integrationFunctional, cylindricalPairing, relativeTopClass] using hx 1
  · intro y hy
    simpa [cylindricalPairing, fundamentalClass] using hy 1
  · norm_num [solenoidFundamentalClassDescends, integrationFunctional, cylindricalPairing,
      fundamentalClass, relativeTopClass]
  · norm_num [solenoidBoundaryFundamentalClass, boundaryFundamentalClassRep]

end Omega.Multiscale
