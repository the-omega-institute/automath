import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Concrete phase-consistent rank-`1` normalization data. The unique free scale is the `SU(2)`
radius `r`, and phase consistency fixes it by requiring the maximal-torus geodesic length
`2 π r` to equal `2 π`. -/
structure PhaseGateRank1VolumeRigidityData where
  su2Radius : ℝ
  phaseConsistentRadius : 2 * Real.pi * su2Radius = 2 * Real.pi

namespace PhaseGateRank1VolumeRigidityData

/-- Phase-consistent `U(1)` volume. -/
def volU1 (_D : PhaseGateRank1VolumeRigidityData) : ℝ :=
  2 * Real.pi

/-- `SU(2) ≃ S³` with radius fixed by phase consistency. -/
def volSU2 (D : PhaseGateRank1VolumeRigidityData) : ℝ :=
  2 * Real.pi ^ 2 * D.su2Radius ^ 3

/-- `SO(3)` is the free twofold quotient of `SU(2)`. -/
def volSO3 (D : PhaseGateRank1VolumeRigidityData) : ℝ :=
  D.volSU2 / 2

/-- `RP¹ = U(1) / {±1}` is the free twofold quotient of the phase circle. -/
def volRP1 (D : PhaseGateRank1VolumeRigidityData) : ℝ :=
  D.volU1 / 2

lemma su2Radius_eq_one (D : PhaseGateRank1VolumeRigidityData) : D.su2Radius = 1 := by
  nlinarith [Real.pi_pos, D.phaseConsistentRadius]

end PhaseGateRank1VolumeRigidityData

open PhaseGateRank1VolumeRigidityData

/-- Paper label: `prop:phase-gate-rank1-volume-rigidity`. The phase-normalized `U(1)` circle has
length `2π`, the induced `SU(2)` volume is `2π²`, and the free twofold quotients halve those
volumes to `π²` and `π`. -/
theorem paper_phase_gate_rank1_volume_rigidity (D : PhaseGateRank1VolumeRigidityData) :
    D.volU1 = 2 * Real.pi ∧ D.volSU2 = 2 * Real.pi ^ 2 ∧ D.volSO3 = Real.pi ^ 2 ∧
      D.volRP1 = Real.pi := by
  have hr : D.su2Radius = 1 := D.su2Radius_eq_one
  have hsu2 : D.volSU2 = 2 * Real.pi ^ 2 := by
    simp [PhaseGateRank1VolumeRigidityData.volSU2, hr]
  refine ⟨rfl, hsu2, ?_, ?_⟩
  · calc
      D.volSO3 = D.volSU2 / 2 := rfl
      _ = (2 * Real.pi ^ 2) / 2 := by rw [hsu2]
      _ = Real.pi ^ 2 := by ring
  · calc
      D.volRP1 = D.volU1 / 2 := rfl
      _ = (2 * Real.pi) / 2 := by rfl
      _ = Real.pi := by ring

end

end Omega.UnitCirclePhaseArithmetic
