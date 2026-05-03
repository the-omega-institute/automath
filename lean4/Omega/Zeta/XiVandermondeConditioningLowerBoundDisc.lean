import Mathlib.Tactic

namespace Omega.Zeta

/-- The two-node Vandermonde determinant. -/
def xi_vandermonde_conditioning_lower_bound_disc_det2 (z₁ z₂ : ℝ) : ℝ :=
  z₂ - z₁

/-- The two-node discriminant factor attached to the Vandermonde determinant square. -/
def xi_vandermonde_conditioning_lower_bound_disc_discriminant2 (z₁ z₂ : ℝ) : ℝ :=
  (z₂ - z₁) ^ 2

/-- Concrete statement for `prop:xi-vandermonde-conditioning-lower-bound-disc`. -/
def xi_vandermonde_conditioning_lower_bound_disc_statement : Prop :=
  ∀ z₁ z₂ σmin σmax detAbs colNorm : ℝ,
    0 < σmin →
      0 < detAbs →
        0 ≤ colNorm →
          σmin ≤ detAbs →
            colNorm ≤ σmax →
              detAbs ^ 2 =
                  xi_vandermonde_conditioning_lower_bound_disc_discriminant2 z₁ z₂ →
                colNorm / detAbs ≤ σmax / σmin ∧
                  xi_vandermonde_conditioning_lower_bound_disc_det2 z₁ z₂ ^ 2 =
                    xi_vandermonde_conditioning_lower_bound_disc_discriminant2 z₁ z₂

theorem paper_xi_vandermonde_conditioning_lower_bound_disc :
    xi_vandermonde_conditioning_lower_bound_disc_statement := by
  intro z₁ z₂ σmin σmax detAbs colNorm hσmin hdet hcol hσle hcolle _hdisc
  have hσmax_nonneg : 0 ≤ σmax := le_trans hcol hcolle
  constructor
  · calc
      colNorm / detAbs ≤ σmax / detAbs := by
        exact div_le_div_of_nonneg_right hcolle hdet.le
      _ ≤ σmax / σmin := by
        exact div_le_div_of_nonneg_left hσmax_nonneg hσmin hσle
  · simp [xi_vandermonde_conditioning_lower_bound_disc_det2,
      xi_vandermonde_conditioning_lower_bound_disc_discriminant2]

end Omega.Zeta
