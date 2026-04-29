import Mathlib

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-oracle-gap-golden-baseline-variance`. -/
theorem paper_conclusion_oracle_gap_golden_baseline_variance
    (A variance : ℝ) (isAffine : Prop)
    (hA :
      A =
        (1 / 2 : ℝ) * (Real.log 2 - Real.log Real.goldenRatio) ^ 2 +
          (1 / 2 : ℝ) * variance)
    (hvar : 0 ≤ variance) (hzero : variance = 0 ↔ isAffine) :
    A =
        (1 / 2 : ℝ) * (Real.log 2 - Real.log Real.goldenRatio) ^ 2 +
          (1 / 2 : ℝ) * variance ∧
      (1 / 2 : ℝ) * (Real.log 2 - Real.log Real.goldenRatio) ^ 2 ≤ A ∧
        (A = (1 / 2 : ℝ) * (Real.log 2 - Real.log Real.goldenRatio) ^ 2 ↔
          isAffine) := by
  refine ⟨hA, ?_, ?_⟩
  · rw [hA]
    nlinarith
  · constructor
    · intro hbase
      apply hzero.mp
      have hhalf : (1 / 2 : ℝ) * variance = 0 := by
        nlinarith
      nlinarith
    · intro haffine
      have hvariance : variance = 0 := hzero.mpr haffine
      rw [hA, hvariance]
      ring

end Omega.Conclusion
