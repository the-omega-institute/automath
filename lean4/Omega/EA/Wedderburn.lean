import Omega.Folding.MomentSum
import Omega.Folding.FiberSpectrum
import Omega.Folding.MomentRecurrence

namespace Omega.EA

/-- Wedderburn total dimension equals S_2(m).
    prop:fold-groupoid-wedderburn -/
theorem wedderburn_total_dim_eq_S2 (m : Nat) :
    ∑ x : X m, (X.fiberMultiplicity x) ^ 2 = momentSum 2 m := rfl

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

end Omega.EA
