import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete Abel-Weil edge data: a dominant conjugate pair, its amplitude, the observed sequence,
and the residual sequence left after removing that pair. -/
structure xi_abel_rightedge_gap_ar2_exp_error_data where
  alpha : ℂ
  amplitude : ℂ
  observable : ℕ → ℂ
  residual : ℕ → ℂ

namespace xi_abel_rightedge_gap_ar2_exp_error_data

/-- The first coefficient of the real quadratic characteristic polynomial. -/
def characteristic_linear (D : xi_abel_rightedge_gap_ar2_exp_error_data) : ℂ :=
  D.alpha + star D.alpha

/-- The constant coefficient of the quadratic characteristic polynomial. -/
def characteristic_constant (D : xi_abel_rightedge_gap_ar2_exp_error_data) : ℂ :=
  D.alpha * star D.alpha

/-- The Abel-Weil expansion with only the right-edge conjugate pair left outside the residual. -/
def right_edge_gap_hypotheses (D : xi_abel_rightedge_gap_ar2_exp_error_data) : Prop :=
  ∀ n : ℕ,
    D.observable n =
      D.amplitude * D.alpha ^ n + star D.amplitude * (star D.alpha) ^ n + D.residual n

/-- The second-order autoregressive defect of the observable. -/
def ar2_defect (D : xi_abel_rightedge_gap_ar2_exp_error_data) (n : ℕ) : ℂ :=
  D.observable (n + 2) - D.characteristic_linear * D.observable (n + 1) +
    D.characteristic_constant * D.observable n

/-- The same autoregressive defect applied only to the residual sequence. -/
def residual_ar2_defect (D : xi_abel_rightedge_gap_ar2_exp_error_data) (n : ℕ) : ℂ :=
  D.residual (n + 2) - D.characteristic_linear * D.residual (n + 1) +
    D.characteristic_constant * D.residual n

/-- After the dominant pair is cancelled, the AR(2) defect is exactly the residual defect. -/
def ar2_exp_error_bound (D : xi_abel_rightedge_gap_ar2_exp_error_data) : Prop :=
  ∀ n : ℕ, D.ar2_defect n = D.residual_ar2_defect n

/-- Both members of the conjugate pair satisfy the quadratic characteristic identity. -/
def coefficient_identities (D : xi_abel_rightedge_gap_ar2_exp_error_data) : Prop :=
  (∀ n : ℕ,
    D.alpha ^ (n + 2) - D.characteristic_linear * D.alpha ^ (n + 1) +
        D.characteristic_constant * D.alpha ^ n =
      0) ∧
    ∀ n : ℕ,
      (star D.alpha) ^ (n + 2) - D.characteristic_linear * (star D.alpha) ^ (n + 1) +
          D.characteristic_constant * (star D.alpha) ^ n =
        0

end xi_abel_rightedge_gap_ar2_exp_error_data

/-- Paper label: `thm:xi-abel-rightedge-gap-ar2-exp-error`. -/
theorem paper_xi_abel_rightedge_gap_ar2_exp_error
    (D : xi_abel_rightedge_gap_ar2_exp_error_data) :
    D.right_edge_gap_hypotheses -> D.ar2_exp_error_bound ∧ D.coefficient_identities := by
  intro hgap
  refine ⟨?_, ?_, ?_⟩
  · intro n
    unfold xi_abel_rightedge_gap_ar2_exp_error_data.ar2_defect
      xi_abel_rightedge_gap_ar2_exp_error_data.residual_ar2_defect
    rw [hgap n, hgap (n + 1), hgap (n + 2)]
    unfold xi_abel_rightedge_gap_ar2_exp_error_data.characteristic_linear
      xi_abel_rightedge_gap_ar2_exp_error_data.characteristic_constant
    ring_nf
  · intro n
    unfold xi_abel_rightedge_gap_ar2_exp_error_data.characteristic_linear
      xi_abel_rightedge_gap_ar2_exp_error_data.characteristic_constant
    ring_nf
  · intro n
    unfold xi_abel_rightedge_gap_ar2_exp_error_data.characteristic_linear
      xi_abel_rightedge_gap_ar2_exp_error_data.characteristic_constant
    ring_nf

end Omega.Zeta
