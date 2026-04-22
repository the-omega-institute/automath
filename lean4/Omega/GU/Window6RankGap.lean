import Omega.Folding.BinFold
import Omega.Folding.FiberArithmeticProperties
import Omega.Conclusion.Window6Collision
import Omega.GU.Window6AbelianizedParityChargeRootCartanSplitting
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.GU

/-- Binary center coordinates contributed by the eight two-point fibers at window `6`. -/
abbrev window6_foldbin_gauge_center_vs_charge_separation_center_binary_dual :=
  Fin (cBinFiberHist 6 2) → Window6F2

/-- Binary charge coordinates coming from all nontrivial fibers at window `6`. -/
abbrev window6_foldbin_gauge_center_vs_charge_separation_charge_binary_dual :=
  Fin (cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4) → Window6F2

/-- Extend a central two-point-fiber charge by zero to the full binary charge lattice. -/
def window6_foldbin_gauge_center_vs_charge_separation_center_to_charge_dual :
    window6_foldbin_gauge_center_vs_charge_separation_center_binary_dual →
      window6_foldbin_gauge_center_vs_charge_separation_charge_binary_dual := fun z i =>
  if h : i.1 < cBinFiberHist 6 2 then z ⟨i.1, h⟩ else 0

lemma window6_foldbin_gauge_center_vs_charge_separation_center_to_charge_dual_injective :
    Function.Injective
      window6_foldbin_gauge_center_vs_charge_separation_center_to_charge_dual := by
  intro z w hzw
  funext i
  have hle : cBinFiberHist 6 2 ≤ cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4 := by
    omega
  let i' :
      Fin (cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4) :=
    ⟨i.1, lt_of_lt_of_le i.2 hle⟩
  have hpoint := congrArg (fun f => f i') hzw
  simpa [window6_foldbin_gauge_center_vs_charge_separation_center_to_charge_dual, i', i.2] using
    hpoint

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

/-- Window-6 foldbin gauge center contributions occupy exactly the two-point-fiber coordinates,
embed into the binary charge lattice, and leave a rank gap of `13`. 
    prop:window6-foldbin-gauge-center-vs-charge-separation -/
theorem paper_window6_foldbin_gauge_center_vs_charge_separation :
    cBinFiberHist 6 2 = 8 ∧
    cBinFiberHist 6 3 = 4 ∧
    cBinFiberHist 6 4 = 9 ∧
    Fintype.card Window6BoundaryParityBlock = 3 ∧
    Fintype.card Window6ParityCoordinate = 21 ∧
    Function.LeftInverse window6BoundaryCartanProjection window6BoundaryCartanInclusion ∧
    Function.Injective window6_foldbin_gauge_center_vs_charge_separation_center_to_charge_dual ∧
    21 - 8 = (13 : ℕ) := by
  rcases paper_window6_abelianized_parity_charge_root_cartan_splitting with
    ⟨_, _, _, _, _, _, _, hBoundary, hParity, hLeft, _⟩
  refine ⟨by rw [cBinFiberHist_6_2], by rw [cBinFiberHist_6_3], by rw [cBinFiberHist_6_4],
    hBoundary, hParity, hLeft,
    window6_foldbin_gauge_center_vs_charge_separation_center_to_charge_dual_injective, by omega⟩

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

/-- Window-6 foldbin gauge center/boundary direct-sum certificate.
    thm:window6-foldbin-gauge-center-boundary-direct-sum -/
theorem paper_window6_foldbin_gauge_center_boundary_direct_sum :
    cBinFiberHist 6 2 = 8 ∧
    cBinFiberHist 6 3 = 4 ∧
    cBinFiberHist 6 4 = 9 ∧
    4 + 9 = 13 ∧
    8 + 13 = 21 ∧
    13 = Nat.fib 7 ∧
    Nat.factorial 2 ^ 8 * Nat.factorial 3 ^ 4 * Nat.factorial 4 ^ 9 =
      2 ^ 8 * 6 ^ 4 * 24 ^ 9 := by
  refine ⟨by rw [cBinFiberHist_6_2], by rw [cBinFiberHist_6_3], by rw [cBinFiberHist_6_4],
    by omega, by omega, by native_decide, Omega.Conclusion.window6_gauge_group_factorial_factors⟩

/-- Window-9 compression ratio: 2^9 / |X_9| = 512 / 89 = 5 rem 67.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_window9_compression_ratio :
    2 ^ 9 = 512 ∧ Fintype.card (X 9) = 89 ∧
    Fintype.card (X 9) = Nat.fib 11 ∧
    512 / 89 = 5 ∧ 512 % 89 = 67 ∧ 5 * 89 < 512 := by
  refine ⟨by norm_num, X.card_X_nine, ?_, by omega, by omega, by omega⟩
  rw [X.card_X_nine]; native_decide

/-- Window-10 compression ratio: 2^10 / |X_10| = 1024 / 144 = 7 rem 16.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_window10_compression_ratio :
    2 ^ 10 = 1024 ∧ Fintype.card (X 10) = 144 ∧
    Fintype.card (X 10) = Nat.fib 12 ∧
    1024 / 144 = 7 ∧ 1024 % 144 = 16 ∧ 7 * 144 < 1024 := by
  refine ⟨by norm_num, X.card_X_ten, ?_, by omega, by omega, by omega⟩
  rw [X.card_X_ten]; native_decide

/-- Complete compression ratio package for windows 6 through 10.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_window_compression_ratio_6_to_10_package :
    (2 ^ 6 = 64 ∧ Fintype.card (X 6) = 21 ∧
     64 / 21 = 3 ∧ 64 % 21 = 1) ∧
    (2 ^ 7 = 128 ∧ Fintype.card (X 7) = 34 ∧
     128 / 34 = 3 ∧ 128 % 34 = 26) ∧
    (2 ^ 8 = 256 ∧ Fintype.card (X 8) = 55 ∧
     256 / 55 = 4 ∧ 256 % 55 = 36) ∧
    (2 ^ 9 = 512 ∧ Fintype.card (X 9) = 89 ∧
     512 / 89 = 5 ∧ 512 % 89 = 67) ∧
    (2 ^ 10 = 1024 ∧ Fintype.card (X 10) = 144 ∧
     1024 / 144 = 7 ∧ 1024 % 144 = 16) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    refine ⟨by norm_num, ?_, by omega, by omega⟩
  · exact X.card_X_six
  · exact X.card_X_seven
  · exact X.card_X_eight
  · exact X.card_X_nine
  · exact X.card_X_ten

/-- Window-11 compression ratio: 2^11 / |X_11| = 2048 / 233 = 8 rem 184.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_window11_compression_ratio :
    2 ^ 11 = 2048 ∧ Fintype.card (X 11) = 233 ∧
    Fintype.card (X 11) = Nat.fib 13 ∧
    2048 / 233 = 8 ∧ 2048 % 233 = 184 ∧ 8 * 233 < 2048 := by
  refine ⟨by norm_num, X.card_X_eleven, ?_, by omega, by omega, by omega⟩
  rw [X.card_X_eleven]; native_decide

/-- Window-12 compression ratio: 2^12 / |X_12| = 4096 / 377 = 10 rem 326.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_window12_compression_ratio :
    2 ^ 12 = 4096 ∧ Fintype.card (X 12) = 377 ∧
    Fintype.card (X 12) = Nat.fib 14 ∧
    4096 / 377 = 10 ∧ 4096 % 377 = 326 ∧ 10 * 377 < 4096 := by
  refine ⟨by norm_num, X.card_X_twelve, ?_, by omega, by omega, by omega⟩
  rw [X.card_X_twelve]; native_decide

/-- Complete compression ratio package for windows 6 through 12.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_window_compression_ratio_6_to_12_package :
    (2 ^ 6 = 64 ∧ Fintype.card (X 6) = 21 ∧ 64 / 21 = 3 ∧ 64 % 21 = 1) ∧
    (2 ^ 7 = 128 ∧ Fintype.card (X 7) = 34 ∧ 128 / 34 = 3 ∧ 128 % 34 = 26) ∧
    (2 ^ 8 = 256 ∧ Fintype.card (X 8) = 55 ∧ 256 / 55 = 4 ∧ 256 % 55 = 36) ∧
    (2 ^ 9 = 512 ∧ Fintype.card (X 9) = 89 ∧ 512 / 89 = 5 ∧ 512 % 89 = 67) ∧
    (2 ^ 10 = 1024 ∧ Fintype.card (X 10) = 144 ∧ 1024 / 144 = 7 ∧ 1024 % 144 = 16) ∧
    (2 ^ 11 = 2048 ∧ Fintype.card (X 11) = 233 ∧ 2048 / 233 = 8 ∧ 2048 % 233 = 184) ∧
    (2 ^ 12 = 4096 ∧ Fintype.card (X 12) = 377 ∧ 4096 / 377 = 10 ∧ 4096 % 377 = 326) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    refine ⟨by norm_num, ?_, by omega, by omega⟩
  · exact X.card_X_six
  · exact X.card_X_seven
  · exact X.card_X_eight
  · exact X.card_X_nine
  · exact X.card_X_ten
  · exact X.card_X_eleven
  · exact X.card_X_twelve

/-- Window-13 compression ratio: 2^13 / |X_13| = 8192 / 610 = 13 rem 262.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_window13_compression_ratio :
    2 ^ 13 = 8192 ∧ Fintype.card (X 13) = 610 ∧
    Fintype.card (X 13) = Nat.fib 15 ∧
    8192 / 610 = 13 ∧ 8192 % 610 = 262 ∧ 13 * 610 < 8192 := by
  refine ⟨by norm_num, X.card_X_thirteen, ?_, by omega, by omega, by omega⟩
  rw [X.card_X_thirteen]; native_decide

/-- Window-13 quotient/remainder witness: 2^13 = 13·F_15 + 262.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_window13_quotient_remainder_witness :
    2 ^ 13 = 13 * Nat.fib 15 + 262 := by native_decide

/-- Complete compression ratio package for windows 6 through 13.
    subsec:bdry-tower-zeck-gut-part1 -/
theorem paper_window_compression_ratio_6_to_13_package :
    (2 ^ 6 = 64 ∧ Fintype.card (X 6) = 21 ∧ 64 / 21 = 3 ∧ 64 % 21 = 1) ∧
    (2 ^ 7 = 128 ∧ Fintype.card (X 7) = 34 ∧ 128 / 34 = 3 ∧ 128 % 34 = 26) ∧
    (2 ^ 8 = 256 ∧ Fintype.card (X 8) = 55 ∧ 256 / 55 = 4 ∧ 256 % 55 = 36) ∧
    (2 ^ 9 = 512 ∧ Fintype.card (X 9) = 89 ∧ 512 / 89 = 5 ∧ 512 % 89 = 67) ∧
    (2 ^ 10 = 1024 ∧ Fintype.card (X 10) = 144 ∧ 1024 / 144 = 7 ∧ 1024 % 144 = 16) ∧
    (2 ^ 11 = 2048 ∧ Fintype.card (X 11) = 233 ∧ 2048 / 233 = 8 ∧ 2048 % 233 = 184) ∧
    (2 ^ 12 = 4096 ∧ Fintype.card (X 12) = 377 ∧ 4096 / 377 = 10 ∧ 4096 % 377 = 326) ∧
    (2 ^ 13 = 8192 ∧ Fintype.card (X 13) = 610 ∧ 8192 / 610 = 13 ∧ 8192 % 610 = 262) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    refine ⟨by norm_num, ?_, by omega, by omega⟩
  · exact X.card_X_six
  · exact X.card_X_seven
  · exact X.card_X_eight
  · exact X.card_X_nine
  · exact X.card_X_ten
  · exact X.card_X_eleven
  · exact X.card_X_twelve
  · exact X.card_X_thirteen

end Omega.GU
