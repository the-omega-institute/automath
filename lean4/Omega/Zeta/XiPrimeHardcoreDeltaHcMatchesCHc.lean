import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete `t = 1` prime-hardcore normalization ledger.  The quotient identity records the
hard-core constant as the zeta quotient times the ZG density. -/
structure xi_prime_hardcore_deltahc_matches_c_hc_data where
  deltaHCAtOne : ℝ
  hardcoreConstant : ℝ
  zetaEulerQuotient : ℝ
  deltaZG : ℝ
  deltaHCAtOne_eq_hardcoreConstant : deltaHCAtOne = hardcoreConstant
  zetaEulerQuotient_ne_zero : zetaEulerQuotient ≠ 0
  zetaQuotient_identity : hardcoreConstant = zetaEulerQuotient * deltaZG

/-- Paper-facing statement that the `t = 1` prime-hardcore constant matches `C_HC`. -/
def xi_prime_hardcore_deltahc_matches_c_hc_statement
    (D : xi_prime_hardcore_deltahc_matches_c_hc_data) : Prop :=
  D.deltaHCAtOne = D.hardcoreConstant ∧
    D.deltaZG = D.deltaHCAtOne / D.zetaEulerQuotient

/-- Paper label: `cor:xi-prime-hardcore-deltaHC-matches-C_HC`. -/
theorem paper_xi_prime_hardcore_deltahc_matches_c_hc
    (D : xi_prime_hardcore_deltahc_matches_c_hc_data) :
    xi_prime_hardcore_deltahc_matches_c_hc_statement D := by
  constructor
  · exact D.deltaHCAtOne_eq_hardcoreConstant
  · calc
      D.deltaZG = D.hardcoreConstant / D.zetaEulerQuotient := by
        rw [D.zetaQuotient_identity]
        field_simp [D.zetaEulerQuotient_ne_zero]
      _ = D.deltaHCAtOne / D.zetaEulerQuotient := by rw [D.deltaHCAtOne_eq_hardcoreConstant]

end

end Omega.Zeta
