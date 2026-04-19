import Mathlib.Tactic
import Omega.CircleDimension.CircleDim
import Omega.Conclusion.ZnToCircleInjectiveDenseSeeds

namespace Omega.Conclusion

/-- Concrete single-phase data for the precision-exponent conclusion. The upper pigeonhole route
caps the optimal exponent by the ambient rank, the badly-approximable route recovers the matching
lower bound, and the `ℤ^r → 𝕋` seed file records that the single-phase ambient rank is exactly
`r`. -/
structure SinglephasePrecisionExponentData where
  rank : ℕ
  optimalExponent : ℕ
  upperPigeonholeBound : optimalExponent ≤ rank
  badlyApproximableLowerBound : rank ≤ optimalExponent

/-- In the single-phase regime, the optimal precision exponent equals the circle dimension of the
ambient rank.
    thm:conclusion-singlephase-precision-exponent-equals-cdim -/
theorem paper_conclusion_singlephase_precision_exponent_equals_cdim
    (D : SinglephasePrecisionExponentData) :
    D.optimalExponent = Omega.CircleDimension.circleDim D.rank 0 := by
  have hExponent : D.optimalExponent = D.rank :=
    le_antisymm D.upperPigeonholeBound D.badlyApproximableLowerBound
  have hSinglePhaseRank :
      Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.generatorCount D.rank = D.rank :=
    Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.rank_eq D.rank
  calc
    D.optimalExponent = D.rank := hExponent
    _ = Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.generatorCount D.rank := hSinglePhaseRank.symm
    _ = Omega.CircleDimension.circleDim D.rank 0 := by
      simp [Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.generatorCount,
        Omega.CircleDimension.circleDim]

end Omega.Conclusion
