import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-discrete-vs-continuous-hair-by-negative-inertia`. The finite-type
equivalence chain identifies boundedness, finite point defect, and rational density; continuous
or infinite hair contradicts finite point defect and therefore forces unbounded inertia. -/
theorem paper_xi_discrete_vs_continuous_hair_by_negative_inertia
    (bounded finitePoint rationalDensity infiniteHair inertiaUnbounded : Prop)
    (hbf : bounded ↔ finitePoint)
    (hfr : finitePoint ↔ rationalDensity)
    (hinf : infiniteHair → ¬ finitePoint)
    (hunbounded : ¬ bounded → inertiaUnbounded) :
    ((bounded ↔ finitePoint) ∧ (finitePoint ↔ rationalDensity) ∧
        (bounded ↔ rationalDensity)) ∧
      (infiniteHair → inertiaUnbounded) := by
  refine ⟨?_, ?_⟩
  · exact ⟨hbf, hfr, hbf.trans hfr⟩
  · intro hHair
    apply hunbounded
    intro hBounded
    exact hinf hHair (hbf.mp hBounded)

end Omega.Zeta
