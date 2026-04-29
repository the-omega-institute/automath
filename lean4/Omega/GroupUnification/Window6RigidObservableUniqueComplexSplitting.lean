import Mathlib.Tactic
import Omega.GroupUnification.Window6CommonRefinementSMLevi
import Omega.GroupUnification.Window6LeviRigidityPatiSalam

namespace Omega.GroupUnification

/-- The neutral adjoint summands in the complexified window-`6` observable:
`(8,1,1)_0 ⊕ (1,3,1)_0 ⊕ (1,1,3)_0 ⊕ (1,1,1)_0`. -/
def window6ComplexNeutralObservableDim : ℕ := 8 + 3 + 3 + 1

/-- The charged pair in the complexified window-`6` observable:
`(3,1,1)_{+q} ⊕ (\bar 3,1,1)_{-q}`. -/
def window6ComplexChargedObservableDim : ℕ := 3 + 3

/-- Total dimension of the audited complex splitting of the rigid window-`6` observable. -/
def window6ComplexObservableDim : ℕ :=
  window6ComplexNeutralObservableDim + window6ComplexChargedObservableDim

/-- Paper-facing wrapper for the audited `21`-dimensional complex splitting of the rigid
window-`6` observable: the Levi skeleton is uniquely Pati-Salam, the light sector closes to the
Standard-Model Levi block, and the resulting complex summands have dimensions
`8 + 3 + 3 + 1 + 3 + 3 = 21`.
    thm:window6-rigid-observable-unique-complex-splitting -/
theorem paper_window6_rigid_observable_unique_complex_splitting :
    window6PatiSalamAdjointDim = 21 ∧
      window6CommonRefinementPatiSalamData.globalFormIsSU4xSU2xSU2 ∧
      window6LightSectorLeviDim = 9 ∧
      window6SMLeviDim = 15 ∧
      window6ComplexNeutralObservableDim = 15 ∧
      window6ComplexChargedObservableDim = 6 ∧
      window6ComplexObservableDim = 21 := by
  rcases paper_window6_levi_rigidity_pati_salam with ⟨hAdjoint, hGlobal⟩
  rcases paper_window6_common_refinement_sm_levi with
    ⟨_, _, _, _, hLight, _, hSM⟩
  refine ⟨hAdjoint, hGlobal, hLight, hSM, ?_, ?_, ?_⟩
  · norm_num [window6ComplexNeutralObservableDim]
  · norm_num [window6ComplexChargedObservableDim]
  · norm_num [window6ComplexObservableDim, window6ComplexNeutralObservableDim,
      window6ComplexChargedObservableDim]

end Omega.GroupUnification
