import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Concrete wrapper for the explicit collision-branch cubic package. -/
structure real_input_40_collision_branch_radius_data where
  real_input_40_collision_branch_radius_unit : Unit := ()

/-- The chapter-local cubic used to model collision-pressure branch formation. -/
def real_input_40_collision_branch_radius_cubic (u x : ℚ) : ℚ :=
  x ^ (3 : ℕ) - 3 * x + (u - 5 / 2)

/-- The derivative of the cubic with respect to the spectral variable. -/
def real_input_40_collision_branch_radius_cubic_deriv (x : ℚ) : ℚ :=
  3 * x ^ (2 : ℕ) - 3

/-- The explicit cubic discriminant factorization. -/
def real_input_40_collision_branch_radius_discriminant (u : ℚ) : ℚ :=
  -27 * (u - 1 / 2) * (u - 9 / 2)

/-- The real logarithm of the left branch point `u = 1 / 2`. -/
def real_input_40_collision_branch_radius_theta_left : ℝ :=
  -Real.log 2

/-- The real logarithm of the right branch point `u = 9 / 2`. -/
def real_input_40_collision_branch_radius_theta_right : ℝ :=
  Real.log (9 / 2 : ℝ)

/-- The radius from `θ = 0` to the nearest real logarithmic branch point. -/
def real_input_40_collision_branch_radius_taylor_radius : ℝ :=
  min |real_input_40_collision_branch_radius_theta_left|
    |real_input_40_collision_branch_radius_theta_right|

namespace real_input_40_collision_branch_radius_data

/-- The branch points are exactly the `u`-values where the cubic and its derivative share a root,
and these coincide with the explicit discriminant roots. -/
def branch_points_are_discriminant_roots
    (_D : real_input_40_collision_branch_radius_data) : Prop :=
  real_input_40_collision_branch_radius_cubic (1 / 2) (-1) = 0 ∧
    real_input_40_collision_branch_radius_cubic_deriv (-1) = 0 ∧
    real_input_40_collision_branch_radius_discriminant (1 / 2) = 0 ∧
    real_input_40_collision_branch_radius_cubic (9 / 2) 1 = 0 ∧
    real_input_40_collision_branch_radius_cubic_deriv 1 = 0 ∧
    real_input_40_collision_branch_radius_discriminant (9 / 2) = 0

/-- Lifting the two positive branch points through `u = exp θ` gives the real branch lattice seen
from the `θ`-plane. -/
def theta_branch_lattice (_D : real_input_40_collision_branch_radius_data) : Prop :=
  Real.exp real_input_40_collision_branch_radius_theta_left = (1 / 2 : ℝ) ∧
    Real.exp real_input_40_collision_branch_radius_theta_right = (9 / 2 : ℝ)

/-- The Taylor radius at `θ = 0` is the distance to the nearest logarithmic branch point. -/
def taylor_radius_formula (_D : real_input_40_collision_branch_radius_data) : Prop :=
  real_input_40_collision_branch_radius_taylor_radius = Real.log 2

end real_input_40_collision_branch_radius_data

open real_input_40_collision_branch_radius_data

/-- Paper label: `cor:real-input-40-collision-branch-radius`. For the explicit cubic
`x^3 - 3x + (u - 5/2)`, the common roots of `f_u` and `f_u'` occur at `(u, x) = (1/2, -1)` and
`(9/2, 1)`, so the discriminant roots lift under `u = exp θ` to the two real branch points
`θ = -log 2` and `θ = log (9/2)`, and the nearest one has radius `log 2`. -/
theorem paper_real_input_40_collision_branch_radius
    (D : real_input_40_collision_branch_radius_data) :
    D.branch_points_are_discriminant_roots ∧
      D.theta_branch_lattice ∧
      D.taylor_radius_formula := by
  refine ⟨?_, ?_, ?_⟩
  · unfold branch_points_are_discriminant_roots
      real_input_40_collision_branch_radius_cubic
      real_input_40_collision_branch_radius_cubic_deriv
      real_input_40_collision_branch_radius_discriminant
    norm_num
  · unfold theta_branch_lattice
      real_input_40_collision_branch_radius_theta_left
      real_input_40_collision_branch_radius_theta_right
    constructor
    · have htwo : (0 : ℝ) < 2 := by norm_num
      calc
        Real.exp (-Real.log 2) = (Real.exp (Real.log 2))⁻¹ := by rw [Real.exp_neg]
        _ = (2 : ℝ)⁻¹ := by rw [Real.exp_log htwo]
        _ = (1 / 2 : ℝ) := by norm_num
    · have hpos : (0 : ℝ) < 9 / 2 := by norm_num
      rw [Real.exp_log hpos]
  · unfold taylor_radius_formula
      real_input_40_collision_branch_radius_taylor_radius
      real_input_40_collision_branch_radius_theta_left
      real_input_40_collision_branch_radius_theta_right
    have hlog2_nonneg : 0 ≤ Real.log 2 := by
      exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hlog92_nonneg : 0 ≤ Real.log (9 / 2 : ℝ) := by
      exact Real.log_nonneg (by norm_num : (1 : ℝ) ≤ (9 / 2 : ℝ))
    have hlog_le : Real.log 2 ≤ Real.log (9 / 2 : ℝ) := by
      exact Real.strictMonoOn_log.monotoneOn (by simp) (by norm_num) (by norm_num)
    have hneg : -Real.log 2 ≤ 0 := by linarith
    simpa [abs_of_nonpos hneg, abs_of_nonneg hlog92_nonneg] using min_eq_left hlog_le

end

end Omega.SyncKernelRealInput
