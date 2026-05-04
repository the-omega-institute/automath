import Mathlib.Tactic
import Omega.Conclusion.DeepfrozenMicroescortOracleThreshold

namespace Omega.Conclusion

noncomputable section

/-- Concrete rate data for comparing the uniform-input lower bitrate with the frozen
microescort threshold.  The two inequalities are the oracle-capacity upper estimate and the
Fibonacci growth lower estimate, expressed as comparable real rates. -/
structure conclusion_uniform_vs_frozen_micro_bitrate_separation_data where
  conclusion_uniform_vs_frozen_micro_bitrate_separation_frozenAlpha : Nat
  conclusion_uniform_vs_frozen_micro_bitrate_separation_budgetBeta : Nat
  conclusion_uniform_vs_frozen_micro_bitrate_separation_uniformInputBitrate : ℝ
  conclusion_uniform_vs_frozen_micro_bitrate_separation_oracleCapacityUpper : ℝ
  conclusion_uniform_vs_frozen_micro_bitrate_separation_fibonacciGrowthLower : ℝ
  conclusion_uniform_vs_frozen_micro_bitrate_separation_fibonacci_le_oracle :
    conclusion_uniform_vs_frozen_micro_bitrate_separation_fibonacciGrowthLower ≤
      conclusion_uniform_vs_frozen_micro_bitrate_separation_oracleCapacityUpper
  conclusion_uniform_vs_frozen_micro_bitrate_separation_oracle_le_uniform :
    conclusion_uniform_vs_frozen_micro_bitrate_separation_oracleCapacityUpper ≤
      conclusion_uniform_vs_frozen_micro_bitrate_separation_uniformInputBitrate

/-- Uniform-input lower bound forced by the Fibonacci growth lower estimate and the
oracle-capacity upper estimate. -/
def conclusion_uniform_vs_frozen_micro_bitrate_separation_uniformLowerBound
    (D : conclusion_uniform_vs_frozen_micro_bitrate_separation_data) : Prop :=
  D.conclusion_uniform_vs_frozen_micro_bitrate_separation_fibonacciGrowthLower ≤
    D.conclusion_uniform_vs_frozen_micro_bitrate_separation_uniformInputBitrate

/-- Frozen microescort threshold law imported from the fixed-confidence frozen oracle theorem. -/
def conclusion_uniform_vs_frozen_micro_bitrate_separation_frozenThreshold
    (D : conclusion_uniform_vs_frozen_micro_bitrate_separation_data) : Prop :=
  (∀ m,
    binfoldFrozenEscortReducedSuccess
        D.conclusion_uniform_vs_frozen_micro_bitrate_separation_frozenAlpha
        D.conclusion_uniform_vs_frozen_micro_bitrate_separation_budgetBeta m =
      min
          ((2 : ℝ) ^
            (D.conclusion_uniform_vs_frozen_micro_bitrate_separation_frozenAlpha * m))
          ((2 : ℝ) ^
            (D.conclusion_uniform_vs_frozen_micro_bitrate_separation_budgetBeta * m)) /
        (2 : ℝ) ^
          (D.conclusion_uniform_vs_frozen_micro_bitrate_separation_frozenAlpha * m)) ∧
    ((D.conclusion_uniform_vs_frozen_micro_bitrate_separation_budgetBeta <
        D.conclusion_uniform_vs_frozen_micro_bitrate_separation_frozenAlpha) →
      Filter.Tendsto
        (fun m =>
          binfoldFrozenEscortReducedSuccess
            D.conclusion_uniform_vs_frozen_micro_bitrate_separation_frozenAlpha
            D.conclusion_uniform_vs_frozen_micro_bitrate_separation_budgetBeta m)
        Filter.atTop (nhds 0)) ∧
    ((D.conclusion_uniform_vs_frozen_micro_bitrate_separation_frozenAlpha <
        D.conclusion_uniform_vs_frozen_micro_bitrate_separation_budgetBeta) →
      Filter.Tendsto
        (fun m =>
          binfoldFrozenEscortReducedSuccess
            D.conclusion_uniform_vs_frozen_micro_bitrate_separation_frozenAlpha
            D.conclusion_uniform_vs_frozen_micro_bitrate_separation_budgetBeta m)
        Filter.atTop (nhds 1))

/-- Paper-facing uniform-vs-frozen micro-bitrate separation statement. -/
def conclusion_uniform_vs_frozen_micro_bitrate_separation_statement
    (D : conclusion_uniform_vs_frozen_micro_bitrate_separation_data) : Prop :=
  conclusion_uniform_vs_frozen_micro_bitrate_separation_uniformLowerBound D ∧
    conclusion_uniform_vs_frozen_micro_bitrate_separation_frozenThreshold D

/-- Paper label: `thm:conclusion-uniform-vs-frozen-micro-bitrate-separation`. -/
theorem paper_conclusion_uniform_vs_frozen_micro_bitrate_separation
    (D : conclusion_uniform_vs_frozen_micro_bitrate_separation_data) :
    conclusion_uniform_vs_frozen_micro_bitrate_separation_statement D := by
  constructor
  · exact le_trans
      D.conclusion_uniform_vs_frozen_micro_bitrate_separation_fibonacci_le_oracle
      D.conclusion_uniform_vs_frozen_micro_bitrate_separation_oracle_le_uniform
  · exact paper_conclusion_deepfrozen_microescort_oracle_threshold
      D.conclusion_uniform_vs_frozen_micro_bitrate_separation_frozenAlpha
      D.conclusion_uniform_vs_frozen_micro_bitrate_separation_budgetBeta

end

end Omega.Conclusion
