import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete Abel data for the no finite-order exponential-lock corollary. -/
structure xi_abel_natural_boundary_no_finite_order_exp_lock_data where
  xi_abel_natural_boundary_no_finite_order_exp_lock_order : ℕ
  xi_abel_natural_boundary_no_finite_order_exp_lock_coeff :
    Fin (xi_abel_natural_boundary_no_finite_order_exp_lock_order + 1) → ℂ
  xi_abel_natural_boundary_no_finite_order_exp_lock_error : ℕ → ℂ
  xi_abel_natural_boundary_no_finite_order_exp_lock_abelGeneratingFunction : ℂ → ℂ
  xi_abel_natural_boundary_no_finite_order_exp_lock_boundaryPoint : ℂ
  xi_abel_natural_boundary_no_finite_order_exp_lock_onUnitCircle :
    ‖xi_abel_natural_boundary_no_finite_order_exp_lock_boundaryPoint‖ = 1
  xi_abel_natural_boundary_no_finite_order_exp_lock_continuationAcross : ℂ → Prop
  xi_abel_natural_boundary_no_finite_order_exp_lock_lockForcesContinuation :
    (∃ C theta : ℝ,
      0 < theta ∧ theta < 1 ∧
        (∀ n : ℕ,
          ‖∑ j : Fin (xi_abel_natural_boundary_no_finite_order_exp_lock_order + 1),
              xi_abel_natural_boundary_no_finite_order_exp_lock_coeff j *
                xi_abel_natural_boundary_no_finite_order_exp_lock_error (n + j)‖ ≤
            C * theta ^ n) ∧
          ∃ j : Fin (xi_abel_natural_boundary_no_finite_order_exp_lock_order + 1),
            xi_abel_natural_boundary_no_finite_order_exp_lock_coeff j ≠ 0) →
      xi_abel_natural_boundary_no_finite_order_exp_lock_continuationAcross
        xi_abel_natural_boundary_no_finite_order_exp_lock_boundaryPoint
  xi_abel_natural_boundary_no_finite_order_exp_lock_naturalBoundary :
    ¬ xi_abel_natural_boundary_no_finite_order_exp_lock_continuationAcross
      xi_abel_natural_boundary_no_finite_order_exp_lock_boundaryPoint

/-- Constant-coefficient polynomial shift applied to the Abel coefficient error sequence. -/
noncomputable def xi_abel_natural_boundary_no_finite_order_exp_lock_polynomial_shift
    (D : xi_abel_natural_boundary_no_finite_order_exp_lock_data) (n : ℕ) : ℂ :=
  ∑ j : Fin (D.xi_abel_natural_boundary_no_finite_order_exp_lock_order + 1),
    D.xi_abel_natural_boundary_no_finite_order_exp_lock_coeff j *
      D.xi_abel_natural_boundary_no_finite_order_exp_lock_error (n + j)

/-- A nonzero finite-order constant-coefficient relation with strictly exponential residual. -/
def xi_abel_natural_boundary_no_finite_order_exp_lock_finite_order_exp_lock
    (D : xi_abel_natural_boundary_no_finite_order_exp_lock_data) : Prop :=
  ∃ C theta : ℝ,
    0 < theta ∧ theta < 1 ∧
      (∀ n : ℕ,
        ‖xi_abel_natural_boundary_no_finite_order_exp_lock_polynomial_shift D n‖ ≤
          C * theta ^ n) ∧
        ∃ j : Fin (D.xi_abel_natural_boundary_no_finite_order_exp_lock_order + 1),
          D.xi_abel_natural_boundary_no_finite_order_exp_lock_coeff j ≠ 0

/-- Paper-facing statement for `cor:xi-abel-natural-boundary-no-finite-order-exp-lock`. -/
def xi_abel_natural_boundary_no_finite_order_exp_lock_statement
    (D : xi_abel_natural_boundary_no_finite_order_exp_lock_data) : Prop :=
  ¬ xi_abel_natural_boundary_no_finite_order_exp_lock_finite_order_exp_lock D

/-- Paper label: `cor:xi-abel-natural-boundary-no-finite-order-exp-lock`. -/
theorem paper_xi_abel_natural_boundary_no_finite_order_exp_lock
    (D : xi_abel_natural_boundary_no_finite_order_exp_lock_data) :
    xi_abel_natural_boundary_no_finite_order_exp_lock_statement D := by
  intro hlock
  apply D.xi_abel_natural_boundary_no_finite_order_exp_lock_naturalBoundary
  exact D.xi_abel_natural_boundary_no_finite_order_exp_lock_lockForcesContinuation hlock

end Omega.Zeta
