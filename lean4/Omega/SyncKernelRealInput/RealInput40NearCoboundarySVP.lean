import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open scoped BigOperators

/-- The three real twist coordinates used in the near-coboundary window. -/
abbrev real_input_40_near_coboundary_svp_angle_vector := Fin 3 → ℝ

/-- Integer residue-class representatives for the wrapped twists. -/
abbrev real_input_40_near_coboundary_svp_index_vector := Fin 3 → ℤ

/-- The trivial wrapped index. -/
def real_input_40_near_coboundary_svp_zero_index :
    real_input_40_near_coboundary_svp_index_vector := fun _ => 0

/-- The quadratic form attached to the Hessian `Σ`. -/
def real_input_40_near_coboundary_svp_quadratic_form_from_matrix
    (hessian : Matrix (Fin 3) (Fin 3) ℝ)
    (theta : real_input_40_near_coboundary_svp_angle_vector) : ℝ :=
  ∑ i, theta i * ∑ j, hessian i j * theta j

/-- Concrete bookkeeping for the quadratic-decay and shortest-vector package. -/
structure real_input_40_near_coboundary_svp_data where
  real_input_40_near_coboundary_svp_hessian : Matrix (Fin 3) (Fin 3) ℝ
  real_input_40_near_coboundary_svp_wrappedAngle :
    real_input_40_near_coboundary_svp_index_vector →
      real_input_40_near_coboundary_svp_angle_vector
  real_input_40_near_coboundary_svp_logRatio :
    real_input_40_near_coboundary_svp_angle_vector → ℝ
  real_input_40_near_coboundary_svp_worstIndex :
    real_input_40_near_coboundary_svp_index_vector
  real_input_40_near_coboundary_svp_quadratic_decay_holds :
    ∀ theta : real_input_40_near_coboundary_svp_angle_vector,
      real_input_40_near_coboundary_svp_logRatio theta =
        -((1 : ℝ) / 2) *
          real_input_40_near_coboundary_svp_quadratic_form_from_matrix
            real_input_40_near_coboundary_svp_hessian theta
  real_input_40_near_coboundary_svp_worstIndex_nonzero :
    real_input_40_near_coboundary_svp_worstIndex ≠
      real_input_40_near_coboundary_svp_zero_index
  real_input_40_near_coboundary_svp_shortest_vector_principle :
    ∀ j : real_input_40_near_coboundary_svp_index_vector,
      j ≠ real_input_40_near_coboundary_svp_zero_index →
        real_input_40_near_coboundary_svp_quadratic_form_from_matrix
            real_input_40_near_coboundary_svp_hessian
            (real_input_40_near_coboundary_svp_wrappedAngle
              real_input_40_near_coboundary_svp_worstIndex) ≤
          real_input_40_near_coboundary_svp_quadratic_form_from_matrix
            real_input_40_near_coboundary_svp_hessian
            (real_input_40_near_coboundary_svp_wrappedAngle j)

namespace real_input_40_near_coboundary_svp_data

/-- The local quadratic-decay package for the twisted spectral radius. -/
def log_spectral_radius_quadratic_decay (D : real_input_40_near_coboundary_svp_data) : Prop :=
  ∀ theta : real_input_40_near_coboundary_svp_angle_vector,
    D.real_input_40_near_coboundary_svp_logRatio theta =
      -((1 : ℝ) / 2) *
        real_input_40_near_coboundary_svp_quadratic_form_from_matrix
          D.real_input_40_near_coboundary_svp_hessian theta

/-- The wrapped index minimizing the `Σ`-quadratic form controls the worst nontrivial twist. -/
def shortest_wrapped_index_controls_worst_twist
    (D : real_input_40_near_coboundary_svp_data) : Prop :=
  D.real_input_40_near_coboundary_svp_worstIndex ≠
      real_input_40_near_coboundary_svp_zero_index ∧
    ∀ j : real_input_40_near_coboundary_svp_index_vector,
      j ≠ real_input_40_near_coboundary_svp_zero_index →
        real_input_40_near_coboundary_svp_quadratic_form_from_matrix
            D.real_input_40_near_coboundary_svp_hessian
            (D.real_input_40_near_coboundary_svp_wrappedAngle
              D.real_input_40_near_coboundary_svp_worstIndex) ≤
          real_input_40_near_coboundary_svp_quadratic_form_from_matrix
            D.real_input_40_near_coboundary_svp_hessian
            (D.real_input_40_near_coboundary_svp_wrappedAngle j)

end real_input_40_near_coboundary_svp_data

open real_input_40_near_coboundary_svp_data

/-- Paper label: `thm:real-input-40-near-coboundary-svp`. -/
theorem paper_real_input_40_near_coboundary_svp (D : real_input_40_near_coboundary_svp_data) :
    D.log_spectral_radius_quadratic_decay ∧
      D.shortest_wrapped_index_controls_worst_twist := by
  exact ⟨D.real_input_40_near_coboundary_svp_quadratic_decay_holds,
    ⟨D.real_input_40_near_coboundary_svp_worstIndex_nonzero,
      D.real_input_40_near_coboundary_svp_shortest_vector_principle⟩⟩

end Omega.SyncKernelRealInput
