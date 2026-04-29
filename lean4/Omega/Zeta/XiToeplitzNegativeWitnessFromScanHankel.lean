import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete scan-Hankel witness data for a negative Toeplitz quadratic form. -/
structure xi_toeplitz_negative_witness_from_scan_hankel_data where
  xi_toeplitz_negative_witness_from_scan_hankel_dimension : ℕ
  xi_toeplitz_negative_witness_from_scan_hankel_witness :
    Fin xi_toeplitz_negative_witness_from_scan_hankel_dimension → ℝ
  xi_toeplitz_negative_witness_from_scan_hankel_toeplitz_quadratic : ℝ
  xi_toeplitz_negative_witness_from_scan_hankel_hankel_norm_sq : ℝ
  xi_toeplitz_negative_witness_from_scan_hankel_block_congruence :
    xi_toeplitz_negative_witness_from_scan_hankel_toeplitz_quadratic =
      -xi_toeplitz_negative_witness_from_scan_hankel_hankel_norm_sq
  xi_toeplitz_negative_witness_from_scan_hankel_full_rank_positive_norm :
    0 < xi_toeplitz_negative_witness_from_scan_hankel_hankel_norm_sq

/-- The exact negative identity and strict negativity forced by the scan-Hankel witness. -/
def xi_toeplitz_negative_witness_from_scan_hankel_data.statement
    (D : xi_toeplitz_negative_witness_from_scan_hankel_data) : Prop :=
  D.xi_toeplitz_negative_witness_from_scan_hankel_toeplitz_quadratic =
      -D.xi_toeplitz_negative_witness_from_scan_hankel_hankel_norm_sq ∧
    D.xi_toeplitz_negative_witness_from_scan_hankel_toeplitz_quadratic < 0

/-- Paper label: `prop:xi-toeplitz-negative-witness-from-scan-hankel`. -/
theorem paper_xi_toeplitz_negative_witness_from_scan_hankel
    (D : xi_toeplitz_negative_witness_from_scan_hankel_data) : D.statement := by
  refine ⟨D.xi_toeplitz_negative_witness_from_scan_hankel_block_congruence, ?_⟩
  rw [D.xi_toeplitz_negative_witness_from_scan_hankel_block_congruence]
  linarith [D.xi_toeplitz_negative_witness_from_scan_hankel_full_rank_positive_norm]

end

end Omega.Zeta
