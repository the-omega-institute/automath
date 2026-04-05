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

end Omega.EA
