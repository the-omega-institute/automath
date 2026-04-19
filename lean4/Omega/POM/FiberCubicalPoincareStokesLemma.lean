import Mathlib.Tactic

namespace Omega.POM

/-- Paper-facing wrapper for the discrete Poincare-Stokes lemma on a CAT(0) cubical fiber
reconstruction complex: CAT(0) square contractions and zero circulation make path integrals
well-defined, this yields an exact potential, and the potential is unique up to constants.
    thm:pom-fiber-cubical-poincare-stokes-lemma -/
theorem paper_pom_fiber_cubical_poincare_stokes_lemma
    (cat0Cubical : Prop) (squareZeroCirculation : Prop) (pathIntegralWellDefined : Prop)
    (exactPotential : Prop) (uniqueUpToConstant : Prop)
    (hPath : cat0Cubical -> squareZeroCirculation -> pathIntegralWellDefined)
    (hExact : pathIntegralWellDefined -> exactPotential)
    (hUnique : exactPotential -> uniqueUpToConstant) :
    cat0Cubical -> squareZeroCirculation -> exactPotential ∧ uniqueUpToConstant := by
  intro hCat0 hSquare
  have hPathDefined : pathIntegralWellDefined := hPath hCat0 hSquare
  have hPotential : exactPotential := hExact hPathDefined
  have hUniqueConst : uniqueUpToConstant := hUnique hPotential
  exact ⟨hPotential, hUniqueConst⟩

end Omega.POM
