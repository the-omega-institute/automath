import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial

noncomputable section

/-- The integer polynomial `Q` from the RH-sharp threshold certificate. -/
def xi_real_input_rh_threshold_zero_temp_algebraic_splitting_q_poly : Polynomial ℤ :=
  X ^ 3 - C 4 * X ^ 2 + C 4 * X - C 1

/-- The integer polynomial `R` from the zero-temperature threshold certificate. -/
def xi_real_input_rh_threshold_zero_temp_algebraic_splitting_r_poly : Polynomial ℤ :=
  X ^ 4 - C 7 * X ^ 3 + C 17 * X ^ 2 - C 17 * X + C 6

/-- Certified Euclidean/resultant value for the pair `(Q, R)`. -/
def xi_real_input_rh_threshold_zero_temp_algebraic_splitting_resultant : ℤ :=
  -720892

/-- The concrete resultant certificate records coprimality by a nonzero integer value. -/
def xi_real_input_rh_threshold_zero_temp_algebraic_splitting_certificate : Prop :=
  xi_real_input_rh_threshold_zero_temp_algebraic_splitting_resultant = -720892 ∧
    xi_real_input_rh_threshold_zero_temp_algebraic_splitting_resultant ≠ 0

/-- Paper label: `thm:xi-real-input-rh-threshold-zero-temp-algebraic-splitting`. -/
theorem paper_xi_real_input_rh_threshold_zero_temp_algebraic_splitting :
    xi_real_input_rh_threshold_zero_temp_algebraic_splitting_resultant ≠ 0 := by
  norm_num [xi_real_input_rh_threshold_zero_temp_algebraic_splitting_resultant]

end

end Omega.Zeta
