import Mathlib.Tactic

namespace Omega.Multiscale

/-- Chapter-local data for the shift invariance of the normalized bulk and boundary integrals on a
solenoidal inverse limit. The package keeps the normalized-degree and one-step pullback witnesses
from the earlier wrapper while also recording explicit `n`-layer and `(n + 1)`-layer formulas for
bulk and boundary representatives. -/
structure SolenoidShiftInvarianceData where
  normalizedDegreeFormula : Prop
  oneStepPullback : Prop
  boundaryOneStepPullback : Prop
  bulkIntegral : ℕ → ℝ
  bulkShiftedIntegral : ℕ → ℝ
  boundaryIntegral : ℕ → ℝ
  boundaryShiftedIntegral : ℕ → ℝ
  shiftInvariantIntegral : Prop
  boundaryShiftInvariantIntegral : Prop
  normalizedDegreeFormula_h : normalizedDegreeFormula
  oneStepPullback_h : oneStepPullback
  boundaryOneStepPullback_h : boundaryOneStepPullback
  bulkLayerFormula :
    ∀ n, bulkIntegral n = bulkShiftedIntegral n
  bulkNextLayerFormula :
    ∀ n, bulkShiftedIntegral n = bulkIntegral (n + 1)
  boundaryLayerFormula :
    ∀ n, boundaryIntegral n = boundaryShiftedIntegral n
  boundaryNextLayerFormula :
    ∀ n, boundaryShiftedIntegral n = boundaryIntegral (n + 1)
  deriveShiftInvariantIntegral :
    normalizedDegreeFormula →
      oneStepPullback →
      (∀ n, bulkIntegral n = bulkIntegral (n + 1)) →
      shiftInvariantIntegral
  deriveBoundaryShiftInvariantIntegral :
    normalizedDegreeFormula →
      boundaryOneStepPullback →
      (∀ n, boundaryIntegral n = boundaryIntegral (n + 1)) →
      boundaryShiftInvariantIntegral

/-- Compatibility alias for the earlier wrapper naming. -/
def SolenoidShiftInvarianceData.interiorShiftInvariant (D : SolenoidShiftInvarianceData) : Prop :=
  D.shiftInvariantIntegral

/-- Compatibility alias for the earlier wrapper naming. -/
def SolenoidShiftInvarianceData.boundaryShiftInvariant
    (D : SolenoidShiftInvarianceData) : Prop :=
  D.boundaryShiftInvariantIntegral

/-- Paper-facing wrapper for the shift invariance of the normalized Stokes functionals on the
solenoidal inverse limit: the normalized degree formula, the one-step pullback identities, and the
agreement between the `n`-layer and `(n + 1)`-layer representatives yield the interior and
boundary invariance statements.
    prop:app-solenoid-shift-invariance -/
theorem paper_app_solenoid_shift_invariance (D : SolenoidShiftInvarianceData) :
    D.shiftInvariantIntegral ∧ D.boundaryShiftInvariantIntegral := by
  have hBulk : ∀ n, D.bulkIntegral n = D.bulkIntegral (n + 1) := fun n =>
    (D.bulkLayerFormula n).trans (D.bulkNextLayerFormula n)
  have hBoundary : ∀ n, D.boundaryIntegral n = D.boundaryIntegral (n + 1) := fun n =>
    (D.boundaryLayerFormula n).trans (D.boundaryNextLayerFormula n)
  exact ⟨D.deriveShiftInvariantIntegral D.normalizedDegreeFormula_h D.oneStepPullback_h hBulk,
    D.deriveBoundaryShiftInvariantIntegral
      D.normalizedDegreeFormula_h D.boundaryOneStepPullback_h hBoundary⟩

/-- Compatibility wrapper for the earlier conclusion names. -/
theorem paper_app_solenoid_shift_invariance_legacy (D : SolenoidShiftInvarianceData) :
    D.interiorShiftInvariant ∧ D.boundaryShiftInvariant := by
  simpa [SolenoidShiftInvarianceData.interiorShiftInvariant,
    SolenoidShiftInvarianceData.boundaryShiftInvariant] using
    paper_app_solenoid_shift_invariance D

end Omega.Multiscale
