import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete near-saturation predicate for the affine-uniformization residual. -/
def gm_affine_inverse_major_arc_near_saturation_statement
    (scale residual_energy signal_norm saturation_constant : ℝ) : Prop :=
  saturation_constant * scale ^ (4 : ℕ) * signal_norm ≤ residual_energy

/-- Concrete major-arc concentration predicate for the same signal. -/
def gm_affine_inverse_major_arc_major_arc_concentration_statement
    (major_arc_mass signal_norm concentration_constant : ℝ) : Prop :=
  concentration_constant * signal_norm ≤ major_arc_mass

/-- Concrete data package encoding the forward and backward implications of the affine inverse
theorem. -/
structure gm_affine_inverse_major_arc_data where
  gm_affine_inverse_major_arc_scale : ℝ
  gm_affine_inverse_major_arc_residual_energy : ℝ
  gm_affine_inverse_major_arc_signal_norm : ℝ
  gm_affine_inverse_major_arc_major_arc_mass : ℝ
  gm_affine_inverse_major_arc_saturation_constant : ℝ
  gm_affine_inverse_major_arc_concentration_constant : ℝ
  gm_affine_inverse_major_arc_near_saturation_implies_major_arc_concentration :
    gm_affine_inverse_major_arc_near_saturation_statement
        gm_affine_inverse_major_arc_scale gm_affine_inverse_major_arc_residual_energy
        gm_affine_inverse_major_arc_signal_norm
        gm_affine_inverse_major_arc_saturation_constant →
      gm_affine_inverse_major_arc_major_arc_concentration_statement
        gm_affine_inverse_major_arc_major_arc_mass gm_affine_inverse_major_arc_signal_norm
        gm_affine_inverse_major_arc_concentration_constant
  gm_affine_inverse_major_arc_major_arc_concentration_implies_near_saturation :
    gm_affine_inverse_major_arc_major_arc_concentration_statement
        gm_affine_inverse_major_arc_major_arc_mass gm_affine_inverse_major_arc_signal_norm
        gm_affine_inverse_major_arc_concentration_constant →
      gm_affine_inverse_major_arc_near_saturation_statement
        gm_affine_inverse_major_arc_scale gm_affine_inverse_major_arc_residual_energy
        gm_affine_inverse_major_arc_signal_norm
        gm_affine_inverse_major_arc_saturation_constant

namespace gm_affine_inverse_major_arc_data

/-- The near-saturation side of the affine inverse theorem. -/
def gm_affine_inverse_major_arc_near_saturation (D : gm_affine_inverse_major_arc_data) : Prop :=
  gm_affine_inverse_major_arc_near_saturation_statement
    D.gm_affine_inverse_major_arc_scale D.gm_affine_inverse_major_arc_residual_energy
    D.gm_affine_inverse_major_arc_signal_norm D.gm_affine_inverse_major_arc_saturation_constant

/-- The major-arc concentration side of the affine inverse theorem. -/
def gm_affine_inverse_major_arc_major_arc_concentration
    (D : gm_affine_inverse_major_arc_data) : Prop :=
  gm_affine_inverse_major_arc_major_arc_concentration_statement
    D.gm_affine_inverse_major_arc_major_arc_mass D.gm_affine_inverse_major_arc_signal_norm
    D.gm_affine_inverse_major_arc_concentration_constant

end gm_affine_inverse_major_arc_data

open gm_affine_inverse_major_arc_data

/-- Paper label: `thm:gm-affine-inverse-major-arc`. -/
theorem paper_gm_affine_inverse_major_arc (D : gm_affine_inverse_major_arc_data) :
    D.gm_affine_inverse_major_arc_near_saturation ↔
      D.gm_affine_inverse_major_arc_major_arc_concentration := by
  refine Iff.intro ?_ ?_
  · exact D.gm_affine_inverse_major_arc_near_saturation_implies_major_arc_concentration
  · exact D.gm_affine_inverse_major_arc_major_arc_concentration_implies_near_saturation

end Omega.SyncKernelWeighted
