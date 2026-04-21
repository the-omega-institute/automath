import Mathlib.Tactic
import Omega.Kronecker.W1RightShiftedMinimizer

namespace Omega.Kronecker

/-- Paper label: `thm:xi-kronecker-w1-single-box-optimal-centering`. -/
theorem paper_xi_kronecker_w1_single_box_optimal_centering (q : Nat) (hq : 2 <= q) :
    kroneckerRightShiftedMinimizerSpec q ∧
      kroneckerRightShiftedMinimum q =
        (((5 * q - 1 : Nat) : ℚ) / ((8 * q * (2 * q - 1) : Nat) : ℚ)) ∧
      kroneckerRightShiftedMinimum q < (1 : ℚ) / (2 * q) := by
  have hspec := paper_xi_kronecker_w1_right_shifted_minimizer q hq
  rcases paper_xi_kronecker_star_discrepancy_w1_branching q hq with
    ⟨_, _, hmin, _, _⟩
  refine ⟨hspec, hmin, ?_⟩
  rw [hmin]
  have hq_pos : 0 < q := by omega
  have h2qm1_pos : 0 < 2 * q - 1 := by omega
  have hbigden_pos_nat : 0 < 8 * q * (2 * q - 1) := by
    exact Nat.mul_pos (Nat.mul_pos (by decide) hq_pos) h2qm1_pos
  have htwoq_pos_nat : 0 < 2 * q := by omega
  have h5q1_cast : (((5 * q - 1 : Nat) : ℚ)) = 5 * (q : ℚ) - 1 := by
    have h : 1 ≤ 5 * q := by omega
    rw [Nat.cast_sub h]
    norm_num [Nat.cast_mul]
  have h2qm1_cast : (((2 * q - 1 : Nat) : ℚ)) = 2 * (q : ℚ) - 1 := by
    have h : 1 ≤ 2 * q := by omega
    rw [Nat.cast_sub h]
    norm_num [Nat.cast_mul]
  have hmul :
      (((5 * q - 1 : Nat) : ℚ)) * (((2 * q : Nat) : ℚ)) <
        (((8 * q * (2 * q - 1) : Nat) : ℚ)) := by
    rw [h5q1_cast]
    norm_num [Nat.cast_mul]
    rw [h2qm1_cast]
    ring_nf
    have hq_gt_one : (1 : ℚ) < (q : ℚ) := by
      exact_mod_cast hq
    nlinarith
  have hbigden_pos : (0 : ℚ) < (((8 * q * (2 * q - 1) : Nat) : ℚ)) := by
    exact_mod_cast hbigden_pos_nat
  have htwoq_pos : (0 : ℚ) < (((2 * q : Nat) : ℚ)) := by
    exact_mod_cast htwoq_pos_nat
  have hlt :
      (((5 * q - 1 : Nat) : ℚ) / ((8 * q * (2 * q - 1) : Nat) : ℚ)) <
        (1 : ℚ) / ((2 * q : Nat) : ℚ) := by
    have hbigden_ne : (((8 * q * (2 * q - 1) : Nat) : ℚ)) ≠ 0 := ne_of_gt hbigden_pos
    have htwoq_ne : (((2 * q : Nat) : ℚ)) ≠ 0 := ne_of_gt htwoq_pos
    field_simp [hbigden_ne, htwoq_ne]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  simpa using hlt

end Omega.Kronecker
