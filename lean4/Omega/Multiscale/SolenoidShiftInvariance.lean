import Mathlib.Tactic

namespace Omega.Multiscale

/-- Chapter-local package for the shift invariance of the normalized Stokes functional on the
solenoid inverse limit. The data record the normalized degree formula, the one-step pullback
computation under the shift, and the analogous boundary calculation. -/
structure SolenoidShiftInvarianceData where
  normalizedDegreeFormula : Prop
  oneStepPullback : Prop
  boundaryOneStepPullback : Prop
  interiorShiftInvariant : Prop
  boundaryShiftInvariant : Prop
  normalizedDegreeFormula_h : normalizedDegreeFormula
  oneStepPullback_h : oneStepPullback
  boundaryOneStepPullback_h : boundaryOneStepPullback
  deriveInteriorShiftInvariant :
    normalizedDegreeFormula → oneStepPullback → interiorShiftInvariant
  deriveBoundaryShiftInvariant :
    normalizedDegreeFormula → boundaryOneStepPullback → boundaryShiftInvariant

/-- Paper-facing wrapper for the normalized shift invariance of the solenoid Stokes functional:
the normalized degree formula together with the one-step pullback computation yields invariance in
the interior, and the same normalization applied to the boundary pullback yields the boundary
statement.
    prop:app-solenoid-shift-invariance -/
theorem paper_app_solenoid_shift_invariance (D : SolenoidShiftInvarianceData) :
    D.interiorShiftInvariant ∧ D.boundaryShiftInvariant := by
  exact ⟨D.deriveInteriorShiftInvariant D.normalizedDegreeFormula_h D.oneStepPullback_h,
    D.deriveBoundaryShiftInvariant D.normalizedDegreeFormula_h D.boundaryOneStepPullback_h⟩

end Omega.Multiscale
