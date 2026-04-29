import Omega.CircleDimension.BiphaseAverageFiberDiagonalAntidiagonal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace Omega.CircleDimension

noncomputable section

/-- The biphase average gate in midpoint/difference coordinates. -/
def cdim_biphase_average_disk_critical_ring_gate (u v : ℝ) : ℂ :=
  Complex.exp ((((u + v) / 2 : ℝ) : ℂ) * Complex.I) * (Real.cos ((u - v) / 2) : ℂ)

/-- The midpoint/difference factorization of the biphase average gate. -/
theorem cdim_biphase_average_disk_critical_ring_gate_factor (u v : ℝ) :
    cdim_biphase_average_disk_critical_ring_gate u v =
      Complex.exp (((((u + v) / 2 : ℝ) : ℂ) * Complex.I)) *
        (Real.cos ((u - v) / 2) : ℂ) := by
  rfl

/-- Disk-image record: the gate has the midpoint/difference disk parametrization, contains the
boundary circle, and contains the origin. -/
def cdim_biphase_average_disk_critical_ring_disk_image : Prop :=
  (∀ u v : ℝ,
      cdim_biphase_average_disk_critical_ring_gate u v =
        Complex.exp (((((u + v) / 2 : ℝ) : ℂ) * Complex.I)) *
          (Real.cos ((u - v) / 2) : ℂ)) ∧
    (∀ θ : ℝ,
      cdim_biphase_average_disk_critical_ring_gate θ θ =
        Complex.exp ((θ : ℂ) * Complex.I)) ∧
    (∀ θ : ℝ,
      cdim_biphase_average_disk_critical_ring_gate (θ + Real.pi / 2) (θ - Real.pi / 2) = 0)

/-- The Jacobian determinant in midpoint/difference coordinates. -/
def cdim_biphase_average_disk_critical_ring_jacobian_det (u v : ℝ) : ℝ :=
  Real.sin (u - v) / 2

/-- Critical-locus record: the determinant vanishes on the diagonal and antidiagonal families. -/
def cdim_biphase_average_disk_critical_ring_critical_locus : Prop :=
  (∀ θ : ℝ, cdim_biphase_average_disk_critical_ring_jacobian_det θ θ = 0) ∧
    (∀ θ : ℝ,
      cdim_biphase_average_disk_critical_ring_jacobian_det
        (θ + Real.pi / 2) (θ - Real.pi / 2) = 0)

/-- Critical-value record: the critical families map to the unit circle and to the origin. -/
def cdim_biphase_average_disk_critical_ring_critical_values : Prop :=
  (∀ θ : ℝ,
      cdim_biphase_average_disk_critical_ring_gate θ θ =
        Complex.exp ((θ : ℂ) * Complex.I)) ∧
    (∀ θ : ℝ,
      cdim_biphase_average_disk_critical_ring_gate (θ + Real.pi / 2) (θ - Real.pi / 2) = 0)

/-- Paper label: `thm:cdim-biphase-average-disk-critical-ring`. -/
theorem paper_cdim_biphase_average_disk_critical_ring :
    cdim_biphase_average_disk_critical_ring_disk_image ∧
      cdim_biphase_average_disk_critical_ring_critical_locus ∧
        cdim_biphase_average_disk_critical_ring_critical_values := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro u v
      exact cdim_biphase_average_disk_critical_ring_gate_factor u v
    · intro θ
      rw [cdim_biphase_average_disk_critical_ring_gate_factor]
      have hmid : (((θ + θ) / 2 : ℝ)) = θ := by ring
      simp [hmid]
    · intro θ
      rw [cdim_biphase_average_disk_critical_ring_gate_factor]
      simp
  · refine ⟨?_, ?_⟩
    · intro θ
      simp [cdim_biphase_average_disk_critical_ring_jacobian_det]
    · intro θ
      have hdiff : (θ + Real.pi / 2) - (θ - Real.pi / 2) = Real.pi := by ring
      simp [cdim_biphase_average_disk_critical_ring_jacobian_det, hdiff]
  · refine ⟨?_, ?_⟩
    · intro θ
      rw [cdim_biphase_average_disk_critical_ring_gate_factor]
      have hmid : (((θ + θ) / 2 : ℝ)) = θ := by ring
      simp [hmid]
    · intro θ
      rw [cdim_biphase_average_disk_critical_ring_gate_factor]
      simp

end

end Omega.CircleDimension
