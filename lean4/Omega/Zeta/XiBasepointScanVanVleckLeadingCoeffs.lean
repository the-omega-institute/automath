import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete leading-coefficient package for the Van Vleck identity
`A * y'' - A' * y' = B * y` at infinity.  The two balance fields are the
coefficients of `z^(3κ-2)` and `z^(3κ-3)`, respectively. -/
structure xi_basepoint_scan_van_vleck_leading_coeffs_data where
  kappa : ℝ
  A1 : ℝ
  y1 : ℝ
  b0 : ℝ
  b1 : ℝ
  leadingCoefficientBalance : b0 = kappa * (kappa - 1) - 2 * kappa ^ 2
  subleadingCoefficientBalance :
    b1 + b0 * y1 =
      ((kappa - 1) * (kappa - 2) * y1 + A1 * kappa * (kappa - 1)) -
        (2 * kappa * (kappa - 1) * y1 + (2 * kappa - 1) * A1 * kappa)

/-- The displayed leading and subleading Van Vleck coefficient identities. -/
def xi_basepoint_scan_van_vleck_leading_coeffs_statement
    (D : xi_basepoint_scan_van_vleck_leading_coeffs_data) : Prop :=
  D.b0 = -D.kappa * (D.kappa + 1) ∧
    D.b1 = -D.kappa ^ 2 * D.A1 + 2 * D.y1

/-- Paper label: `prop:xi-basepoint-scan-van-vleck-leading-coeffs`. -/
theorem paper_xi_basepoint_scan_van_vleck_leading_coeffs
    (D : xi_basepoint_scan_van_vleck_leading_coeffs_data) :
    xi_basepoint_scan_van_vleck_leading_coeffs_statement D := by
  constructor
  · rw [D.leadingCoefficientBalance]
    ring
  · have hb0 : D.b0 = -D.kappa * (D.kappa + 1) := by
      rw [D.leadingCoefficientBalance]
      ring
    have hsub := D.subleadingCoefficientBalance
    rw [hb0] at hsub
    nlinarith

end Omega.Zeta
