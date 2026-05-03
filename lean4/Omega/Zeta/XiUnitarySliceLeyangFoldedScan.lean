import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete algebraic data for the unitary-slice Lee--Yang folded scan.

The polynomial is represented by its evaluation function on the relevant real coordinate; the
folded coordinate `X = -1 / y` and the sharp factorization are recorded only at the audited point.
-/
structure xi_unitary_slice_leyang_folded_scan_data where
  xi_unitary_slice_leyang_folded_scan_P : ℝ → ℝ
  xi_unitary_slice_leyang_folded_scan_P_sharp : ℝ → ℝ
  xi_unitary_slice_leyang_folded_scan_S : ℝ
  xi_unitary_slice_leyang_folded_scan_X : ℝ
  xi_unitary_slice_leyang_folded_scan_y : ℝ
  xi_unitary_slice_leyang_folded_scan_X_eq_square :
    xi_unitary_slice_leyang_folded_scan_X =
      xi_unitary_slice_leyang_folded_scan_S ^ (2 : ℕ)
  xi_unitary_slice_leyang_folded_scan_X_eq_neg_inv_y :
    xi_unitary_slice_leyang_folded_scan_X =
      -1 / xi_unitary_slice_leyang_folded_scan_y
  xi_unitary_slice_leyang_folded_scan_sharp_factor :
    xi_unitary_slice_leyang_folded_scan_P_sharp xi_unitary_slice_leyang_folded_scan_X =
      xi_unitary_slice_leyang_folded_scan_P xi_unitary_slice_leyang_folded_scan_S *
        xi_unitary_slice_leyang_folded_scan_P (-xi_unitary_slice_leyang_folded_scan_S)
  xi_unitary_slice_leyang_folded_scan_signed_zero_reflects :
    xi_unitary_slice_leyang_folded_scan_P (-xi_unitary_slice_leyang_folded_scan_S) = 0 →
      xi_unitary_slice_leyang_folded_scan_P xi_unitary_slice_leyang_folded_scan_S = 0

namespace xi_unitary_slice_leyang_folded_scan_data

/-- The concrete zero-event equivalence asserted by the folded scan. -/
def xi_unitary_slice_leyang_folded_scan_statement
    (D : xi_unitary_slice_leyang_folded_scan_data) : Prop :=
  D.xi_unitary_slice_leyang_folded_scan_P D.xi_unitary_slice_leyang_folded_scan_S = 0 ↔
    D.xi_unitary_slice_leyang_folded_scan_P_sharp
      (-1 / D.xi_unitary_slice_leyang_folded_scan_y) = 0

end xi_unitary_slice_leyang_folded_scan_data

open xi_unitary_slice_leyang_folded_scan_data

/-- Paper label: `prop:xi-unitary-slice-leyang-folded-scan`. -/
theorem paper_xi_unitary_slice_leyang_folded_scan
    (D : xi_unitary_slice_leyang_folded_scan_data) :
    D.xi_unitary_slice_leyang_folded_scan_statement := by
  unfold xi_unitary_slice_leyang_folded_scan_statement
  rw [← D.xi_unitary_slice_leyang_folded_scan_X_eq_neg_inv_y]
  rw [D.xi_unitary_slice_leyang_folded_scan_sharp_factor]
  constructor
  · intro hzero
    exact mul_eq_zero_of_left hzero
      (D.xi_unitary_slice_leyang_folded_scan_P (-D.xi_unitary_slice_leyang_folded_scan_S))
  · intro hsharp
    rcases mul_eq_zero.mp hsharp with hzero | hneg
    · exact hzero
    · exact D.xi_unitary_slice_leyang_folded_scan_signed_zero_reflects hneg

end Omega.Zeta
