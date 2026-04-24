import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ComovingDefectBound

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete data for the Jensen-defect/offcritical-shift package: `rho` is the reference radius,
`eps` is the defect upper bound, `r0` is an explicit lower bound for the repulsion radius, and
`delta` is the horizontal offcritical shift. -/
structure JensenDefectControlsOffcriticalShiftData where
  rho : ℝ
  eps : ℝ
  gamma : ℝ
  delta : ℝ
  r0 : ℝ
  hrho : 0 < rho
  hrho_lt_one : rho < 1
  heps : 0 ≤ eps
  hgamma : 0 ≤ gamma
  hdelta : 0 ≤ delta
  hr0_nonneg : 0 ≤ r0
  hr0_le_repulsion : r0 ≤ rho * Real.exp (-eps)
  hdefect_bound : rho * Real.exp (-eps) ≤ (1 - delta) / (1 + delta)

namespace JensenDefectControlsOffcriticalShiftData

/-- The radius obtained from the Jensen-defect bound. -/
noncomputable def repulsionRadius (D : JensenDefectControlsOffcriticalShiftData) : ℝ :=
  D.rho * Real.exp (-D.eps)

/-- A simple explicit shift envelope depending on the certified lower bound `r0`. -/
noncomputable def shiftEnvelope (gamma r : ℝ) : ℝ :=
  gamma + (1 - r) / (1 + r)

/-- The lower bound `r ≥ rho * exp(-eps)` is registered through the explicit witness `r0`. -/
def repulsionRadiusLowerBound (D : JensenDefectControlsOffcriticalShiftData) : Prop :=
  D.r0 ≤ D.repulsionRadius

/-- The offcritical shift is controlled by the explicit envelope `Delta(gamma; r0)`. -/
noncomputable def explicitShiftUpperBound (D : JensenDefectControlsOffcriticalShiftData) : Prop :=
  D.delta ≤ shiftEnvelope D.gamma D.r0

lemma radius_fraction_antitone (D : JensenDefectControlsOffcriticalShiftData) :
    (1 - D.repulsionRadius) / (1 + D.repulsionRadius) ≤ (1 - D.r0) / (1 + D.r0) := by
  have hrep_pos : 0 < D.repulsionRadius := by
    unfold repulsionRadius
    exact mul_pos D.hrho (Real.exp_pos (-D.eps))
  have hden_rep : 0 < 1 + D.repulsionRadius := by linarith
  have hden_r0 : 0 < 1 + D.r0 := by nlinarith [D.hr0_nonneg]
  refine (div_le_div_iff₀ hden_rep hden_r0).2 ?_
  unfold repulsionRadius
  nlinarith [D.hr0_le_repulsion]

end JensenDefectControlsOffcriticalShiftData

open JensenDefectControlsOffcriticalShiftData

/-- Paper label: `thm:app-jensen-defect-controls-offcritical-shift`. The Jensen-defect hypothesis
provides the repulsion-radius lower bound `rho * exp(-eps)`, and the standard defect-to-offset
inequality yields an explicit upper control on the horizontal shift. -/
theorem paper_app_jensen_defect_controls_offcritical_shift
    (D : JensenDefectControlsOffcriticalShiftData) :
    D.repulsionRadiusLowerBound ∧ D.explicitShiftUpperBound := by
  refine ⟨by
    simpa [JensenDefectControlsOffcriticalShiftData.repulsionRadius] using D.hr0_le_repulsion, ?_⟩
  have hdelta_bound :
      D.delta ≤ (1 - D.repulsionRadius) / (1 + D.repulsionRadius) := by
    simpa [JensenDefectControlsOffcriticalShiftData.repulsionRadius] using
      paper_typed_address_biaxial_completion_comoving_defect_bound
        D.hrho D.hrho_lt_one D.heps D.hdelta D.hdefect_bound
  calc
    D.delta ≤ (1 - D.repulsionRadius) / (1 + D.repulsionRadius) := hdelta_bound
    _ ≤ (1 - D.r0) / (1 + D.r0) := D.radius_fraction_antitone
    _ ≤ JensenDefectControlsOffcriticalShiftData.shiftEnvelope D.gamma D.r0 := by
      have hgamma_nonneg : 0 ≤ D.gamma := D.hgamma
      unfold JensenDefectControlsOffcriticalShiftData.shiftEnvelope
      nlinarith

end Omega.TypedAddressBiaxialCompletion
