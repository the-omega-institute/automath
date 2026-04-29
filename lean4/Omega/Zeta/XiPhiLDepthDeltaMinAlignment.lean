import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the closest disk-root/depth conversion.  The disk root is positive and
inside the unit disk, `L` is a logarithmic scale with nonzero logarithm, and the completed-root
field records the real-root correspondence used by the paper normalization. -/
structure xi_phil_depth_delta_min_alignment_data where
  L : ℝ
  diskRoot : ℝ
  completedRoot : ℝ
  L_pos : 0 < L
  logL_ne_zero : Real.log L ≠ 0
  diskRoot_pos : 0 < diskRoot
  diskRoot_lt_one : diskRoot < 1
  completed_root_correspondence : diskRoot + diskRoot⁻¹ = completedRoot

/-- The minimum depth exponent attached to the closest disk root. -/
def xi_phil_depth_delta_min_alignment_delta_min
    (D : xi_phil_depth_delta_min_alignment_data) : ℝ :=
  Real.log (1 / D.diskRoot) / Real.log D.L

/-- The largest disk radius recovered from the minimum depth exponent. -/
def xi_phil_depth_delta_min_alignment_rmax
    (D : xi_phil_depth_delta_min_alignment_data) : ℝ :=
  Real.exp (-(xi_phil_depth_delta_min_alignment_delta_min D) * Real.log D.L)

/-- The thin-layer height corresponding to the largest disk radius. -/
def xi_phil_depth_delta_min_alignment_hmin
    (D : xi_phil_depth_delta_min_alignment_data) : ℝ :=
  1 - xi_phil_depth_delta_min_alignment_rmax D

/-- Closed logarithmic formula for the minimum depth exponent. -/
def xi_phil_depth_delta_min_alignment_data.delta_min_formula
    (D : xi_phil_depth_delta_min_alignment_data) : Prop :=
  xi_phil_depth_delta_min_alignment_delta_min D =
    Real.log (1 / D.diskRoot) / Real.log D.L

/-- Exponential inversion of the depth exponent recovers the closest disk-root radius. -/
def xi_phil_depth_delta_min_alignment_data.rmax_formula
    (D : xi_phil_depth_delta_min_alignment_data) : Prop :=
  xi_phil_depth_delta_min_alignment_rmax D = D.diskRoot

/-- The height convention is the complement of the largest radius. -/
def xi_phil_depth_delta_min_alignment_data.hmin_formula
    (D : xi_phil_depth_delta_min_alignment_data) : Prop :=
  xi_phil_depth_delta_min_alignment_hmin D = 1 - D.diskRoot

/-- Paper label: `prop:xi-phiL-depth-delta-min-alignment`. -/
theorem paper_xi_phil_depth_delta_min_alignment
    (D : xi_phil_depth_delta_min_alignment_data) :
    D.delta_min_formula ∧ D.rmax_formula ∧ D.hmin_formula := by
  have hdelta : D.delta_min_formula := rfl
  have hexponent :
      -(xi_phil_depth_delta_min_alignment_delta_min D) * Real.log D.L =
        Real.log D.diskRoot := by
    unfold xi_phil_depth_delta_min_alignment_delta_min
    have hlog_inv : Real.log (1 / D.diskRoot) = -Real.log D.diskRoot := by
      rw [one_div, Real.log_inv]
    rw [hlog_inv]
    field_simp [D.logL_ne_zero]
  have hrmax : D.rmax_formula := by
    unfold xi_phil_depth_delta_min_alignment_data.rmax_formula
    unfold xi_phil_depth_delta_min_alignment_rmax
    rw [hexponent]
    exact Real.exp_log D.diskRoot_pos
  refine ⟨hdelta, hrmax, ?_⟩
  unfold xi_phil_depth_delta_min_alignment_data.hmin_formula
  unfold xi_phil_depth_delta_min_alignment_hmin
  rw [hrmax]

end

end Omega.Zeta
