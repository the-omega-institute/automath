import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete audit data for the `w = ±2` transport endpoints and the resultant against `w² - 4`.
The endpoint values are recorded as explicit integer squares, and the resultant is recorded as
their product. -/
structure XiTerminalZmGodelIntegerTransportSquareAuditData where
  a : ℤ
  b : ℤ
  qAtPosTwo : ℤ
  qAtNegTwo : ℤ
  resultantAtWSqMinusFour : ℤ
  qAtPosTwo_eq : qAtPosTwo = (a - b) ^ 2
  qAtNegTwo_eq : qAtNegTwo = (a + b) ^ 2
  resultantAtWSqMinusFour_eq : resultantAtWSqMinusFour = qAtPosTwo * qAtNegTwo

/-- Paper label: `thm:xi-terminal-zm-godel-integer-transport-square-audit`. At `w = ±2` the
quadratic transport factor specializes to `(a z ∓ b)²`, so the cleared-denominator endpoint
values are integer squares. Their product is therefore a square as well, and the audit records
that this product is exactly the resultant against `w² - 4`. -/
theorem paper_xi_terminal_zm_godel_integer_transport_square_audit
    (D : XiTerminalZmGodelIntegerTransportSquareAuditData) :
    IsSquare D.qAtPosTwo ∧ IsSquare D.qAtNegTwo ∧ IsSquare D.resultantAtWSqMinusFour := by
  have hPos : IsSquare D.qAtPosTwo := by
    rw [D.qAtPosTwo_eq]
    exact IsSquare.sq (D.a - D.b)
  have hNeg : IsSquare D.qAtNegTwo := by
    rw [D.qAtNegTwo_eq]
    exact IsSquare.sq (D.a + D.b)
  have hRes : IsSquare D.resultantAtWSqMinusFour := by
    rw [D.resultantAtWSqMinusFour_eq]
    exact hPos.mul hNeg
  exact ⟨hPos, hNeg, hRes⟩

end Omega.Zeta
