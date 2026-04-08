import Omega.Folding.MomentSum
import Omega.Folding.FiberSpectrum
import Omega.Folding.MomentRecurrence
import Omega.Folding.MomentTriple
import Omega.Folding.FiberArithmetic

namespace Omega.EA

/-- Wedderburn total dimension equals S_2(m).
    prop:fold-groupoid-wedderburn -/
theorem wedderburn_total_dim_eq_S2 (m : Nat) :
    ∑ x : X m, (X.fiberMultiplicity x) ^ 2 = momentSum 2 m := rfl

/-- Paper-facing q=2 fiber-index CGF specialization.
    prop:pom-fiber-index-cgf -/
theorem paper_pom_fiber_index_cgf_q2_specialized (m : Nat) :
    (∑ x : X m, X.fiberMultiplicity x ^ 2 = momentSum 2 m) ∧
    (∑ x : X m, X.fiberMultiplicity x = 2 ^ m) := by
  refine ⟨wedderburn_total_dim_eq_S2 m, ?_⟩
  exact X.fiberMultiplicity_total m

/-- q=3 POM fiber-index CGF specialization.
    prop:pom-fiber-index-cgf -/
theorem paper_pom_fiber_index_cgf_q3_specialized (m : Nat) :
    (∑ x : X m, X.fiberMultiplicity x ^ 3 = momentSum 3 m) ∧
    (∑ x : X m, X.fiberMultiplicity x = 2 ^ m) := by
  refine ⟨rfl, ?_⟩
  exact X.fiberMultiplicity_total m

/-- q=4 POM fiber-index CGF specialization.
    prop:pom-fiber-index-cgf -/
theorem paper_pom_fiber_index_cgf_q4_specialized (m : Nat) :
    (∑ x : X m, X.fiberMultiplicity x ^ 4 = momentSum 4 m) ∧
    (∑ x : X m, X.fiberMultiplicity x = 2 ^ m) := by
  refine ⟨rfl, ?_⟩
  exact X.fiberMultiplicity_total m

/-- General q POM fiber-index CGF.
    prop:pom-fiber-index-cgf -/
theorem paper_pom_fiber_index_cgf_general (q m : Nat) :
    ∑ x : X m, (X.fiberMultiplicity x) ^ q = momentSum q m := rfl

/-- Complete POM fiber-index CGF package.
    prop:pom-fiber-index-cgf -/
theorem paper_pom_fiber_index_cgf_package :
    (∀ m, ∑ x : X m, X.fiberMultiplicity x ^ 2 = momentSum 2 m) ∧
    (∀ m, ∑ x : X m, X.fiberMultiplicity x ^ 3 = momentSum 3 m) ∧
    (∀ m, ∑ x : X m, X.fiberMultiplicity x ^ 4 = momentSum 4 m) ∧
    (∀ q m, ∑ x : X m, (X.fiberMultiplicity x) ^ q = momentSum q m) ∧
    (∀ m, ∑ x : X m, X.fiberMultiplicity x = 2 ^ m) :=
  ⟨wedderburn_total_dim_eq_S2,
   fun _ => rfl,
   fun _ => rfl,
   paper_pom_fiber_index_cgf_general,
   X.fiberMultiplicity_total⟩

/-- At m=6, the groupoid algebra has Wedderburn dimension 220.
    prop:fold-groupoid-wedderburn -/
theorem wedderburn_dim_m6 : momentSum 2 6 = 220 := momentSum_two_six

/-- Cached fiber histogram at m=6: 2 with d=1, 4 with d=2, 8 with d=3, 5 with d=4, 2 with d=5.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem fiber_histogram_m6 :
    cFiberHist 6 1 = 2 ∧ cFiberHist 6 2 = 4 ∧ cFiberHist 6 3 = 8 ∧ cFiberHist 6 4 = 5 ∧
    cFiberHist 6 5 = 2 := by
  exact ⟨cFiberHist_6_1, cFiberHist_6_2, cFiberHist_6_3, cFiberHist_6_4, cFiberHist_6_5⟩

/-- At m=7, the groupoid algebra has Wedderburn dimension 544.
    prop:fold-groupoid-wedderburn -/
theorem wedderburn_dim_m7 : momentSum 2 7 = 544 := momentSum_two_seven

/-- At m=8, the groupoid algebra has Wedderburn dimension 1352.
    prop:fold-groupoid-wedderburn -/
theorem wedderburn_dim_m8 : momentSum 2 8 = 1352 := momentSum_two_eight_rec

-- ══════════════════════════════════════════════════════════════
-- Phase R295: Sector dimension sum, Wedderburn growth certificate
-- ══════════════════════════════════════════════════════════════

/-- Sector dimension sum at m=6: S_2=220, |X_6|=F_8=21, avg=10, histogram sums.
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem paper_sector_dimension_sum_m6 :
    momentSum 2 6 = 220 ∧
    momentSum 0 6 = 21 ∧
    220 / 21 = 10 ∧
    cFiberHist 6 1 + cFiberHist 6 2 + cFiberHist 6 3 + cFiberHist 6 4 + cFiberHist 6 5 = 21 := by
  refine ⟨momentSum_two_six, ?_, by omega, ?_⟩
  · rw [momentSum_zero]; native_decide
  · rw [cFiberHist_6_1, cFiberHist_6_2, cFiberHist_6_3, cFiberHist_6_4, cFiberHist_6_5]

/-- Wedderburn dimension growth certificate: S_2 grows by factor ~2.5.
    prop:fold-groupoid-wedderburn -/
theorem paper_ea_wedderburn_growth_certificate :
    momentSum 2 6 = 220 ∧ momentSum 2 7 = 544 ∧ momentSum 2 8 = 1352 ∧
    2 * 220 < 544 ∧ 544 < 3 * 220 ∧
    2 * 544 < 1352 ∧ 1352 < 3 * 544 := by
  refine ⟨momentSum_two_six, wedderburn_dim_m7, wedderburn_dim_m8, by omega, by omega,
    by omega, by omega⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R305: Wedderburn dim m=9,10 + growth certificate
-- ══════════════════════════════════════════════════════════════

/-- prop:fold-groupoid-wedderburn -/
theorem wedderburn_dim_m9 : momentSum 2 9 = 3352 := momentSum_two_nine_rec

/-- prop:fold-groupoid-wedderburn -/
theorem wedderburn_dim_m10 : momentSum 2 10 = 8320 := momentSum_two_ten_rec

/-- prop:fold-groupoid-wedderburn -/
theorem paper_ea_wedderburn_growth_extended :
    momentSum 2 6 = 220 ∧ momentSum 2 7 = 544 ∧ momentSum 2 8 = 1352 ∧
    momentSum 2 9 = 3352 ∧ momentSum 2 10 = 8320 ∧
    2 * 220 < 544 ∧ 544 < 3 * 220 ∧
    2 * 544 < 1352 ∧ 1352 < 3 * 544 ∧
    2 * 1352 < 3352 ∧ 3352 < 3 * 1352 ∧
    2 * 3352 < 8320 ∧ 8320 < 3 * 3352 := by
  refine ⟨momentSum_two_six, momentSum_two_seven, momentSum_two_eight_rec,
    momentSum_two_nine_rec, momentSum_two_ten_rec,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- prop:fold-groupoid-wedderburn -/
theorem wedderburn_avg_fiber_m7 : momentSum 2 7 / Nat.fib 9 = 16 := by
  rw [momentSum_two_seven]; native_decide

/-- Paper: prop:fold-groupoid-wedderburn (m=7 average fiber).
    prop:fold-groupoid-wedderburn -/
theorem paper_wedderburn_avg_fiber_m7 :
    momentSum 2 7 / Nat.fib 9 = 16 := by
  simpa using wedderburn_avg_fiber_m7

-- ══════════════════════════════════════════════════════════════
-- Phase R308: Wedderburn dim m=11,12 + ratio tightening
-- ══════════════════════════════════════════════════════════════

/-- prop:fold-groupoid-wedderburn -/
theorem wedderburn_dim_m11 : momentSum 2 11 = 20640 := momentSum_two_eleven_rec

/-- prop:fold-groupoid-wedderburn -/
theorem wedderburn_dim_m12 : momentSum 2 12 = 51216 := momentSum_two_twelve_rec

/-- S_2 ratio between 12/5 and 13/5 for m=8..11. prop:fold-groupoid-wedderburn -/
theorem paper_ea_wedderburn_ratio_tightening :
    12 * 1352 < 5 * 3352 ∧ 12 * 3352 < 5 * 8320 ∧
    12 * 8320 < 5 * 20640 ∧ 12 * 20640 < 5 * 51216 ∧
    5 * 3352 < 13 * 1352 ∧ 5 * 8320 < 13 * 3352 ∧
    5 * 20640 < 13 * 8320 ∧ 5 * 51216 < 13 * 20640 := by omega

-- ══════════════════════════════════════════════════════════════
-- Phase R311: S_2 factorization certificates
-- ══════════════════════════════════════════════════════════════

/-- prop:fold-groupoid-wedderburn -/
theorem momentSum_two_six_factored : momentSum 2 6 = 4 * 5 * 11 := by
  rw [momentSum_two_six]

/-- prop:fold-groupoid-wedderburn -/
theorem momentSum_two_seven_factored : momentSum 2 7 = 32 * 17 := by
  rw [momentSum_two_seven]

/-- prop:fold-groupoid-wedderburn -/
theorem momentSum_two_eight_factored : momentSum 2 8 = 8 * 13 ^ 2 := by
  rw [momentSum_two_eight_rec]; norm_num

/-- prop:fold-groupoid-wedderburn -/
theorem momentSum_two_nine_factored : momentSum 2 9 = 8 * 419 := by
  rw [momentSum_two_nine_rec]

/-- prop:fold-groupoid-wedderburn -/
theorem prime_419 : Nat.Prime 419 := by native_decide

/-- Paper package. prop:fold-groupoid-wedderburn -/
theorem paper_ea_s2_factorization :
    momentSum 2 6 = 4 * 5 * 11 ∧ momentSum 2 7 = 32 * 17 ∧
    momentSum 2 8 = 8 * 13 ^ 2 ∧ momentSum 2 9 = 8 * 419 ∧ Nat.Prime 419 := by
  exact ⟨momentSum_two_six_factored, momentSum_two_seven_factored,
    momentSum_two_eight_factored, momentSum_two_nine_factored, prime_419⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R320: Wedderburn dimension ratio exactness
-- ══════════════════════════════════════════════════════════════

/-- At m=7, S_2 = 16 · F_9 (exact ratio).
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem wedderburn_dim_ratio_m7_exact :
    momentSum 2 7 = 16 * Nat.fib 9 := by
  rw [momentSum_two_seven]; native_decide

/-- At m=6, S_2 is not divisible by F_8 (no exact ratio).
    thm:fold-groupoid-z2x2-central-idempotents -/
theorem wedderburn_dim_ratio_m6_not_exact :
    momentSum 2 6 % Nat.fib 8 ≠ 0 := by
  rw [momentSum_two_six]; native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R331: S_2 factored m=10,11,12
-- ══════════════════════════════════════════════════════════════

/-- S_2(10) = 2^7 · 5 · 13 = 8320.
    prop:fold-groupoid-wedderburn -/
theorem momentSum_two_ten_factored : momentSum 2 10 = 2 ^ 7 * 5 * 13 := by
  rw [momentSum_two_ten_rec]; norm_num

/-- S_2(11) = 2^5 · 3 · 5 · 43 = 20640.
    prop:fold-groupoid-wedderburn -/
theorem momentSum_two_eleven_factored : momentSum 2 11 = 2 ^ 5 * 3 * 5 * 43 := by
  rw [momentSum_two_eleven_rec]; norm_num

/-- S_2(12) = 2^4 · 3 · 11 · 97 = 51216.
    prop:fold-groupoid-wedderburn -/
theorem momentSum_two_twelve_factored : momentSum 2 12 = 2 ^ 4 * 3 * 11 * 97 := by
  rw [momentSum_two_twelve_rec]; norm_num

/-- Wedderburn dimension S_2(13) = 127072.
    prop:fold-groupoid-wedderburn -/
theorem wedderburn_dim_m13 : momentSum 2 13 = 127072 := momentSum_two_thirteen_rec

/-- Wedderburn dimension S_2(14) = 315296.
    prop:fold-groupoid-wedderburn -/
theorem wedderburn_dim_m14 : momentSum 2 14 = 315296 := momentSum_two_fourteen_rec

/-- Wedderburn dimension S_2(15) = 782304.
    prop:fold-groupoid-wedderburn -/
theorem wedderburn_dim_m15 : momentSum 2 15 = 782304 := momentSum_two_fifteen_rec

/-- Paper package: Wedderburn dimensions m = 13, 14, 15 with growth witnesses.
    prop:fold-groupoid-wedderburn -/
theorem paper_wedderburn_dim_m13_m14_m15_package :
    momentSum 2 13 = 127072 ∧
    momentSum 2 14 = 315296 ∧
    momentSum 2 15 = 782304 ∧
    momentSum 2 13 < momentSum 2 14 ∧
    momentSum 2 14 < momentSum 2 15 ∧
    2 * momentSum 2 13 < momentSum 2 14 ∧
    2 * momentSum 2 14 < momentSum 2 15 := by
  refine ⟨wedderburn_dim_m13, wedderburn_dim_m14, wedderburn_dim_m15, ?_, ?_, ?_, ?_⟩
  · rw [wedderburn_dim_m13, wedderburn_dim_m14]; omega
  · rw [wedderburn_dim_m14, wedderburn_dim_m15]; omega
  · rw [wedderburn_dim_m13, wedderburn_dim_m14]; omega
  · rw [wedderburn_dim_m14, wedderburn_dim_m15]; omega

/-- Wedderburn dimension S_2(16) = 1941056.
    prop:fold-groupoid-wedderburn -/
theorem wedderburn_dim_m16 : momentSum 2 16 = 1941056 := momentSum_two_sixteen_rec

/-- Wedderburn dimension S_2(17) = 4816128.
    prop:fold-groupoid-wedderburn -/
theorem wedderburn_dim_m17 : momentSum 2 17 = 4816128 := momentSum_two_seventeen_rec

/-- Paper package: Wedderburn dimensions m = 16, 17 with growth witnesses.
    prop:fold-groupoid-wedderburn -/
theorem paper_wedderburn_dim_m16_m17_growth_package :
    momentSum 2 16 = 1941056 ∧
    momentSum 2 17 = 4816128 ∧
    momentSum 2 15 < momentSum 2 16 ∧
    momentSum 2 16 < momentSum 2 17 ∧
    2 * momentSum 2 15 < momentSum 2 16 ∧
    2 * momentSum 2 16 < momentSum 2 17 := by
  refine ⟨wedderburn_dim_m16, wedderburn_dim_m17, ?_, ?_, ?_, ?_⟩
  · rw [wedderburn_dim_m15, wedderburn_dim_m16]; omega
  · rw [wedderburn_dim_m16, wedderburn_dim_m17]; omega
  · rw [wedderburn_dim_m15, wedderburn_dim_m16]; omega
  · rw [wedderburn_dim_m16, wedderburn_dim_m17]; omega

end Omega.EA
