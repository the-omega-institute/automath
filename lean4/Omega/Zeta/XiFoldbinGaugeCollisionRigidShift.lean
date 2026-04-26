import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-scale components in the fold-bin gauge collision normalization. -/
structure xi_foldbin_gauge_collision_rigid_shift_data where
  xi_foldbin_gauge_collision_rigid_shift_escortKL : ℝ
  xi_foldbin_gauge_collision_rigid_shift_stirlingGaugeVolume : ℝ
  xi_foldbin_gauge_collision_rigid_shift_constantShift : ℝ
  xi_foldbin_gauge_collision_rigid_shift_exponentialError : ℝ

/-- Collision ledger before subtracting the Stirling gauge volume. -/
def xi_foldbin_gauge_collision_rigid_shift_rawCollision
    (D : xi_foldbin_gauge_collision_rigid_shift_data) : ℝ :=
  D.xi_foldbin_gauge_collision_rigid_shift_escortKL +
    D.xi_foldbin_gauge_collision_rigid_shift_stirlingGaugeVolume +
      D.xi_foldbin_gauge_collision_rigid_shift_constantShift +
        D.xi_foldbin_gauge_collision_rigid_shift_exponentialError

/-- Collision ledger after gauge-volume normalization. -/
def xi_foldbin_gauge_collision_rigid_shift_normalizedCollision
    (D : xi_foldbin_gauge_collision_rigid_shift_data) : ℝ :=
  xi_foldbin_gauge_collision_rigid_shift_rawCollision D -
    D.xi_foldbin_gauge_collision_rigid_shift_stirlingGaugeVolume

/-- The rigid shift left by the gauge-volume subtraction. -/
def xi_foldbin_gauge_collision_rigid_shift_statement
    (D : xi_foldbin_gauge_collision_rigid_shift_data) : Prop :=
  xi_foldbin_gauge_collision_rigid_shift_normalizedCollision D =
    D.xi_foldbin_gauge_collision_rigid_shift_escortKL +
      D.xi_foldbin_gauge_collision_rigid_shift_constantShift +
        D.xi_foldbin_gauge_collision_rigid_shift_exponentialError

/-- Paper label: `cor:xi-foldbin-gauge-collision-rigid-shift`. -/
theorem paper_xi_foldbin_gauge_collision_rigid_shift
    (D : xi_foldbin_gauge_collision_rigid_shift_data) :
    xi_foldbin_gauge_collision_rigid_shift_statement D := by
  unfold xi_foldbin_gauge_collision_rigid_shift_statement
    xi_foldbin_gauge_collision_rigid_shift_normalizedCollision
    xi_foldbin_gauge_collision_rigid_shift_rawCollision
  ring

end Omega.Zeta
