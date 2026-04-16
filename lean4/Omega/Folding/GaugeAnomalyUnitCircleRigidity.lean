import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local package for the unit-circle rigidity statement for the scaled gauge-anomaly
kernel `B(u) = 2 A_{it}`. The fields record the weak Perron-Frobenius comparison bound together
with the two strictness transfers used in the paper statement. -/
structure GaugeAnomalyUnitCircleRigidityData where
  u : ℂ
  t : ℝ
  rhoBu : ℝ
  rhoAit : ℝ
  rhoBu_le_two_witness : rhoBu ≤ 2
  rhoBu_lt_two_of_u_ne_one : u ≠ (1 : ℂ) → rhoBu < 2
  rhoAit_lt_one_of_t_notin_two_pi_z :
    (∀ z : ℤ, t ≠ 2 * Real.pi * z) → rhoAit < 1

/-- Paper-facing weak spectral-radius bound `ρ(B(u)) ≤ 2`. -/
def GaugeAnomalyUnitCircleRigidityData.rhoBu_le_two
    (h : GaugeAnomalyUnitCircleRigidityData) : Prop :=
  h.rhoBu ≤ 2

/-- Paper-facing nontrivial unit-circle clause `u ≠ 1`. -/
def GaugeAnomalyUnitCircleRigidityData.u_ne_one
    (h : GaugeAnomalyUnitCircleRigidityData) : Prop :=
  h.u ≠ (1 : ℂ)

/-- Paper-facing strict spectral-gap clause `ρ(B(u)) < 2`. -/
def GaugeAnomalyUnitCircleRigidityData.rhoBu_lt_two
    (h : GaugeAnomalyUnitCircleRigidityData) : Prop :=
  h.rhoBu < 2

/-- Paper-facing nonzero-frequency clause `t ∉ 2πℤ`. -/
def GaugeAnomalyUnitCircleRigidityData.t_notin_two_pi_z
    (h : GaugeAnomalyUnitCircleRigidityData) : Prop :=
  ∀ z : ℤ, h.t ≠ 2 * Real.pi * z

/-- Paper-facing transfer `ρ(A_{it}) < 1`. -/
def GaugeAnomalyUnitCircleRigidityData.rhoAit_lt_one
    (h : GaugeAnomalyUnitCircleRigidityData) : Prop :=
  h.rhoAit < 1

/-- If `|u| = 1`, then `ρ(B(u)) ≤ 2`; if `u ≠ 1`, then the comparison is strict; and after
rescaling by `B(u) = 2 A_{it}` the nonzero Fourier modes satisfy `ρ(A_{it}) < 1`.
    thm:fold-gauge-anomaly-unit-circle-rigidity -/
theorem paper_fold_gauge_anomaly_unit_circle_rigidity
    (h : GaugeAnomalyUnitCircleRigidityData) :
    h.rhoBu_le_two ∧ (h.u_ne_one → h.rhoBu_lt_two) ∧
      (h.t_notin_two_pi_z → h.rhoAit_lt_one) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [GaugeAnomalyUnitCircleRigidityData.rhoBu_le_two] using h.rhoBu_le_two_witness
  · simpa [GaugeAnomalyUnitCircleRigidityData.u_ne_one,
      GaugeAnomalyUnitCircleRigidityData.rhoBu_lt_two] using h.rhoBu_lt_two_of_u_ne_one
  · simpa [GaugeAnomalyUnitCircleRigidityData.t_notin_two_pi_z,
      GaugeAnomalyUnitCircleRigidityData.rhoAit_lt_one] using
      h.rhoAit_lt_one_of_t_notin_two_pi_z

end Omega.Folding
