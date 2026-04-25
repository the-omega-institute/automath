import Mathlib.Tactic
import Omega.Folding.FoldZeroDivisorTripleReduction
import Omega.Folding.FoldZeroHalfIndexMultiple6

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-sixperiod-deterministic-triple-downshift`. On the congruence
class `m ≡ 4 [MOD 6]`, the half-index zero block supplies the Fibonacci lower bound, and the
stored zero-divisor triple reduction pushes the same lower bound through the four deterministic
collision, KL, peak, and max-fiber estimates. -/
theorem paper_conclusion_sixperiod_deterministic_triple_downshift
    (D : Omega.Folding.FoldZeroDivisorTripleReductionData) (hm : D.m % 6 = 4)
    (hzero : D.zeroLower = (Nat.fib ((D.m + 2) / 2) : ℝ)) :
    let z : ℝ := (Nat.fib ((D.m + 2) / 2) : ℝ)
    Nat.fib ((D.m + 2) / 2) ≤ (Omega.Folding.foldZeroFrequencyUnion D.m).card ∧
      D.col ≤ 1 - z / D.totalFibers ∧
      D.kl ≤ Real.log (D.totalFibers - z) ∧
      D.peak ≤ 2 ^ D.m * Real.sqrt (D.totalFibers - 1 - z) ∧
      D.maxFiberExcess ≤ 2 ^ D.m * Real.sqrt ((D.totalFibers - 1 - z) / D.totalFibers) := by
  dsimp
  have hm_zero : (D.m + 2) % 6 = 0 := by
    omega
  have hzeroCard :
      Nat.fib ((D.m + 2) / 2) ≤ (Omega.Folding.foldZeroFrequencyUnion D.m).card :=
    (Omega.Folding.paper_fold_zero_half_index_multiple6 D.m hm_zero).2
  have htriple := Omega.Folding.paper_fold_zero_divisor_triple_reduction D
  refine ⟨hzeroCard, ?_, ?_, ?_, ?_⟩
  · simpa [hzero] using htriple.1
  · simpa [hzero] using htriple.2.1
  · simpa [hzero] using htriple.2.2.1
  · simpa [hzero] using htriple.2.2.2

end Omega.Conclusion
