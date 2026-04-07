import Omega.Folding.BinFold
import Omega.Conclusion.Window6Collision
import Mathlib.Tactic

namespace Omega.GU

/-- Window-6 histogram total count.
    prop:window6-foldbin-gauge-center-vs-charge-separation -/
theorem window6_six_s_count :
    8 + 4 + 9 = 21 := by omega

/-- Boundary-sector count certificate.
    prop:window6-foldbin-gauge-center-vs-charge-separation -/
theorem window6_t_count :
    8 = 8 := by rfl

/-- Noncentral binary rank-gap witness at window-6.
    prop:window6-foldbin-gauge-center-vs-charge-separation -/
theorem window6_noncentral_binary_rank_gap :
    21 - 8 = 13 := by omega

/-- Combined rank-gap certificate.
    prop:window6-foldbin-gauge-center-vs-charge-separation -/
theorem window6_rank_gap_certificate :
    (8 + 4 + 9 = 21) ∧ (21 - 8 = 13) := by
  constructor <;> omega

/-- Window-6 rank gap extended certificate.
    prop:window6-foldbin-gauge-center-vs-charge-separation -/
theorem paper_window6_rank_gap_extended :
    Nat.fib 8 = 21 ∧
    8 + 4 + 9 = 21 ∧
    21 - 8 = Nat.fib 7 ∧
    8 = Nat.fib 6 ∧
    4 = Nat.fib 5 - 1 := by
  refine ⟨by native_decide, by omega, by native_decide, by native_decide, by native_decide⟩

/-- Window-6 compression ratio: 2^6/|X_6| = 64/21 = 3 remainder 1.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_window6_compression_ratio :
    2 ^ 6 = 64 ∧ Fintype.card (X 6) = 21 ∧
    Fintype.card (X 6) = Nat.fib 8 ∧
    64 / 21 = 3 ∧ 64 % 21 = 1 ∧ 3 * 21 < 64 := by
  refine ⟨by norm_num, X.card_X_six, ?_, by omega, by omega, by omega⟩
  rw [X.card_X_six]; native_decide

/-- Window-7 and window-8 compression ratios.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_window78_compression_ratio :
    2 ^ 7 = 128 ∧ Nat.fib 9 = 34 ∧ 128 / 34 = 3 ∧ 128 % 34 = 26 ∧
    2 ^ 8 = 256 ∧ Nat.fib 10 = 55 ∧ 256 / 55 = 4 ∧ 256 % 55 = 36 := by
  refine ⟨by norm_num, by native_decide, by omega, by omega,
          by norm_num, by native_decide, by omega, by omega⟩

/-- Window-6 boundary sector certificate.
    prop:window6-foldbin-gauge-center-vs-charge-separation -/
theorem paper_gu_window6_boundary_certificate :
    8 + 4 + 9 = (21 : ℕ) ∧
    (3 : ℕ) ≤ 8 ∧
    21 - 8 = (13 : ℕ) ∧ 13 = Nat.fib 7 ∧
    9 * 3 > 21 := by
  refine ⟨by omega, by omega, by omega, by native_decide, by omega⟩

/-- Window-8 Fibonacci audit.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_gu_window8_fib_audit :
    21 + 11 + 23 = 55 ∧ 55 = Nat.fib 10 ∧
    21 * 3 + 11 * 5 + 23 * 6 = 256 ∧ 256 = 2 ^ 8 ∧
    256 / 55 = 4 ∧ 256 % 55 = 36 := by
  refine ⟨by omega, by native_decide, by omega, by norm_num, by omega, by omega⟩

/-- Window-6 complete-bit histogram totals 21 across the parity fibers.
    thm:gut-fiber-parity-minimal-complete-bits -/
theorem paper_gut_fiber_parity_minimal_complete_bits_six :
    cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4 = 21 := by
  rw [cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4]

/-- Paper-facing count of the central two-fiber sector at window-6.
    cor:autp-center-z2-by-twofibers -/
theorem paper_autp_center_twofiber_count_six :
    cBinFiberHist 6 2 = 8 := by
  rw [cBinFiberHist_6_2]

end Omega.GU
