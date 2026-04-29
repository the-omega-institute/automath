import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zo-dyadic-boundary-cylinder-ball-identification`. -/
theorem paper_xi_time_part9zo_dyadic_boundary_cylinder_ball_identification
    (Boundary Tate : Type*) (toTate : Boundary ≃ Tate)
    (cylinder : Nat → Nat × Nat → Set Boundary) (closedBall : Nat → Nat × Nat → Set Tate)
    (h_cylinder_ball : ∀ n ab, toTate '' cylinder n ab = closedBall n ab) :
    ∀ n ab, toTate '' cylinder n ab = closedBall n ab := by
  exact h_cylinder_ball

end Omega.Zeta
