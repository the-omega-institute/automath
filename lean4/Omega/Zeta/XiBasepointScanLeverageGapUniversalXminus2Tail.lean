import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

noncomputable section

/-- The universal tail model residual: only the final kernel coordinate survives to order
`x^{-1}`. -/
def xi_basepoint_scan_leverage_gap_universal_xminus2_tail_residual {m : ℕ}
    (last : Fin m) (x : ℝ) : Fin m → ℝ :=
  fun i => if i = last then x⁻¹ else 0

/-- The leverage-gap quadratic form in the universal tail chart. -/
def xi_basepoint_scan_leverage_gap_universal_xminus2_tail_quadratic {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) (last : Fin m) (x : ℝ) : ℝ :=
  dotProduct (xi_basepoint_scan_leverage_gap_universal_xminus2_tail_residual last x)
    (M.mulVec (xi_basepoint_scan_leverage_gap_universal_xminus2_tail_residual last x))

/-- The leading `x^{-2}` coefficient read off from the last basis direction. -/
def xi_basepoint_scan_leverage_gap_universal_xminus2_tail_leading_coeff {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) (last : Fin m) : ℝ :=
  M last last

lemma xi_basepoint_scan_leverage_gap_universal_xminus2_tail_quadratic_eq {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) (last : Fin m) (x : ℝ) :
    xi_basepoint_scan_leverage_gap_universal_xminus2_tail_quadratic M last x =
      x⁻¹ * (M last last * x⁻¹) := by
  simp [xi_basepoint_scan_leverage_gap_universal_xminus2_tail_quadratic,
    xi_basepoint_scan_leverage_gap_universal_xminus2_tail_residual, dotProduct,
    Matrix.mulVec]

/-- Paper label: `thm:xi-basepoint-scan-leverage-gap-universal-xminus2-tail`.

In the tail chart where the residual vector is exactly `x^{-1}` times the final basis vector,
the leverage-gap quadratic form has leading coefficient given by the final diagonal entry of
the residual moment matrix. -/
theorem paper_xi_basepoint_scan_leverage_gap_universal_xminus2_tail {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) (last : Fin m) (ell : ℝ → ℝ)
    (hquad :
      ∀ x,
        ell x =
          xi_basepoint_scan_leverage_gap_universal_xminus2_tail_quadratic M last x) :
    ∀ x,
      x ≠ 0 →
        x ^ 2 * ell x =
          xi_basepoint_scan_leverage_gap_universal_xminus2_tail_leading_coeff M last := by
  intro x hx
  rw [hquad x, xi_basepoint_scan_leverage_gap_universal_xminus2_tail_quadratic_eq]
  rw [pow_two]
  set a := M last last
  change x * x * (x⁻¹ * (a * x⁻¹)) =
    xi_basepoint_scan_leverage_gap_universal_xminus2_tail_leading_coeff M last
  rw [xi_basepoint_scan_leverage_gap_universal_xminus2_tail_leading_coeff]
  calc
    x * x * (x⁻¹ * (a * x⁻¹)) = (x * x⁻¹) * (x * x⁻¹) * a := by ring
    _ = a := by rw [mul_inv_cancel₀ hx]; ring

end

end Omega.Zeta
