import Mathlib.Tactic

namespace Omega.Zeta

/-- Four joint components for two commuting orthogonal projections.  The fields are the components
in the `(0,0)`, `(1,0)`, `(0,1)`, and `(1,1)` joint eigenspaces. -/
structure xi_poisson_second_order_petz_commuting_square_data where
  xi_poisson_second_order_petz_commuting_square_u00 : ℝ
  xi_poisson_second_order_petz_commuting_square_u10 : ℝ
  xi_poisson_second_order_petz_commuting_square_u01 : ℝ
  xi_poisson_second_order_petz_commuting_square_u11 : ℝ

/-- Coefficient for the range of the first projection. -/
noncomputable def xi_poisson_second_order_petz_commuting_square_CG
    (D : xi_poisson_second_order_petz_commuting_square_data) : ℝ :=
  (D.xi_poisson_second_order_petz_commuting_square_u10 ^ 2 +
    D.xi_poisson_second_order_petz_commuting_square_u11 ^ 2) / 2

/-- Coefficient for the range of the second projection. -/
noncomputable def xi_poisson_second_order_petz_commuting_square_CH
    (D : xi_poisson_second_order_petz_commuting_square_data) : ℝ :=
  (D.xi_poisson_second_order_petz_commuting_square_u01 ^ 2 +
    D.xi_poisson_second_order_petz_commuting_square_u11 ^ 2) / 2

/-- Coefficient for the intersection projection. -/
noncomputable def xi_poisson_second_order_petz_commuting_square_Cinf
    (D : xi_poisson_second_order_petz_commuting_square_data) : ℝ :=
  D.xi_poisson_second_order_petz_commuting_square_u11 ^ 2 / 2

/-- Coefficient for the generated/join projection. -/
noncomputable def xi_poisson_second_order_petz_commuting_square_Csup
    (D : xi_poisson_second_order_petz_commuting_square_data) : ℝ :=
  (D.xi_poisson_second_order_petz_commuting_square_u10 ^ 2 +
      D.xi_poisson_second_order_petz_commuting_square_u01 ^ 2 +
      D.xi_poisson_second_order_petz_commuting_square_u11 ^ 2) /
    2

/-- Monotonicity for included projection ranges and the commuting-square Pythagoras identity. -/
def xi_poisson_second_order_petz_commuting_square_conclusion
    (D : xi_poisson_second_order_petz_commuting_square_data) : Prop :=
  xi_poisson_second_order_petz_commuting_square_Cinf D ≤
      xi_poisson_second_order_petz_commuting_square_CG D ∧
    xi_poisson_second_order_petz_commuting_square_Cinf D ≤
      xi_poisson_second_order_petz_commuting_square_CH D ∧
    xi_poisson_second_order_petz_commuting_square_CG D ≤
      xi_poisson_second_order_petz_commuting_square_Csup D ∧
    xi_poisson_second_order_petz_commuting_square_CH D ≤
      xi_poisson_second_order_petz_commuting_square_Csup D ∧
    xi_poisson_second_order_petz_commuting_square_CG D +
        xi_poisson_second_order_petz_commuting_square_CH D =
      xi_poisson_second_order_petz_commuting_square_Cinf D +
        xi_poisson_second_order_petz_commuting_square_Csup D

/-- Paper label: `thm:xi-poisson-second-order-petz-commuting-square`. -/
theorem paper_xi_poisson_second_order_petz_commuting_square
    (D : xi_poisson_second_order_petz_commuting_square_data) :
    xi_poisson_second_order_petz_commuting_square_conclusion D := by
  unfold xi_poisson_second_order_petz_commuting_square_conclusion
  unfold xi_poisson_second_order_petz_commuting_square_CG
  unfold xi_poisson_second_order_petz_commuting_square_CH
  unfold xi_poisson_second_order_petz_commuting_square_Cinf
  unfold xi_poisson_second_order_petz_commuting_square_Csup
  have h10 : 0 ≤ D.xi_poisson_second_order_petz_commuting_square_u10 ^ 2 := sq_nonneg _
  have h01 : 0 ≤ D.xi_poisson_second_order_petz_commuting_square_u01 ^ 2 := sq_nonneg _
  constructor
  · nlinarith
  constructor
  · nlinarith [sq_nonneg D.xi_poisson_second_order_petz_commuting_square_u11]
  constructor
  · nlinarith
  constructor
  · nlinarith
  · ring

end Omega.Zeta
