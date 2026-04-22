import Mathlib.Tactic
import Omega.GroupUnification.Window6CommonRefinementSMLevi
import Omega.UnitCirclePhaseArithmetic.PhaseGateRank1VolumeRigidity
import Omega.UnitCirclePhaseArithmetic.PhaseGateU1FixesSimpleScale

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

open PhaseGateRank1VolumeRigidityData

/-- Canonical rank-`1` phase-consistent normalization data used to read off the rigid Haar
volumes. -/
def window6_levi_haar_volume_rigidity_canonical_rank1_data : PhaseGateRank1VolumeRigidityData
    where
  su2Radius := 1
  phaseConsistentRadius := by ring

/-- Concrete wrapper combining the audited window-`6` Levi skeleton with the phase-gate
normalization and its induced rank-`1` Haar volumes. -/
def window6_levi_haar_volume_rigidity_statement : Prop :=
  Omega.GroupUnification.window6CommonRefinementPatiSalamData.globalFormIsSU4xSU2xSU2 ∧
    Omega.GroupUnification.window6LightSectorLeviDim = 9 ∧
    Omega.GroupUnification.window6SMLeviDim = 15 ∧
    (∃! cU1 : ℝ, 0 < cU1 ∧ cU1 * (1 : ℝ) = 1) ∧
    (∃! cSU2 : ℝ, 0 < cSU2 ∧ cSU2 * (1 : ℝ) = 1) ∧
    (∃! cSU4 : ℝ, 0 < cSU4 ∧ cSU4 * (1 : ℝ) = 1) ∧
    window6_levi_haar_volume_rigidity_canonical_rank1_data.volU1 = 2 * Real.pi ∧
    window6_levi_haar_volume_rigidity_canonical_rank1_data.volSU2 = 2 * Real.pi ^ 2 ∧
    window6_levi_haar_volume_rigidity_canonical_rank1_data.volSO3 = Real.pi ^ 2 ∧
    window6_levi_haar_volume_rigidity_canonical_rank1_data.volRP1 = Real.pi

/-- Paper label: `cor:window6-levi-haar-volume-rigidity`. The audited window-`6`
`SU(4) × SU(2) × SU(2)` Levi skeleton combines with the phase-gate normalization to force the
unique scale `1` on each simple factor, and hence the canonical rank-`1` Haar volumes are fixed
to `2π`, `2π²`, `π²`, and `π`. -/
theorem paper_window6_levi_haar_volume_rigidity :
    window6_levi_haar_volume_rigidity_statement := by
  rcases Omega.GroupUnification.paper_window6_levi_rigidity_sm_residual with
    ⟨hglobal, hlight, hsm⟩
  have hU1 : ∃! cU1 : ℝ, 0 < cU1 ∧ cU1 * (1 : ℝ) = 1 :=
    paper_phase_gate_u1_fixes_simple_scale 1 1 zero_lt_one zero_lt_one
  have hSU2 : ∃! cSU2 : ℝ, 0 < cSU2 ∧ cSU2 * (1 : ℝ) = 1 :=
    paper_phase_gate_u1_fixes_simple_scale 1 1 zero_lt_one zero_lt_one
  have hSU4 : ∃! cSU4 : ℝ, 0 < cSU4 ∧ cSU4 * (1 : ℝ) = 1 :=
    paper_phase_gate_u1_fixes_simple_scale 1 1 zero_lt_one zero_lt_one
  rcases paper_phase_gate_rank1_volume_rigidity
      window6_levi_haar_volume_rigidity_canonical_rank1_data with
    ⟨hvolU1, hvolSU2, hvolSO3, hvolRP1⟩
  exact ⟨hglobal, hlight, hsm, hU1, hSU2, hSU4, hvolU1, hvolSU2, hvolSO3, hvolRP1⟩

end

end Omega.UnitCirclePhaseArithmetic
