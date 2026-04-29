import Omega.CircleDimension.DerivedChainArithmeticBooleanIntervalGeodesics

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-chain-arithmetic-median-factorial-geodesics`. -/
theorem paper_conclusion_chain_arithmetic_median_factorial_geodesics :
    Omega.CircleDimension.squarefreeMedianCenter 6 10 15 = 30 ∧
      Omega.CircleDimension.derivedChainArithmeticBooleanCubeStructure ∧
      Omega.CircleDimension.derivedChainArithmeticShortestGeodesicsArePermutations ∧
      Omega.CircleDimension.derivedChainArithmeticShortestGeodesicCount =
        Nat.factorial Omega.CircleDimension.derivedChainArithmeticRank := by
  exact ⟨Omega.CircleDimension.paper_derived_chain_arithmetic_median_unique_minimizer.1,
    Omega.CircleDimension.paper_derived_chain_arithmetic_boolean_interval_geodesics.1,
    Omega.CircleDimension.paper_derived_chain_arithmetic_boolean_interval_geodesics.2.1,
    Omega.CircleDimension.paper_derived_chain_arithmetic_boolean_interval_geodesics.2.2⟩

end Omega.Conclusion
