import Omega.Conclusion.LocalizedAnomalyPairwiseSkeletonDeterminesSpectrum

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-localized-anomaly-pairwise-union-product`.

The localized pairwise-union skeleton leaves no higher-order primitive factor, and its certificate
dimension is the cardinality of the unordered pair index set. -/
theorem paper_conclusion_localized_anomaly_pairwise_union_product (r : ℕ) :
    Omega.Conclusion.conclusion_localized_anomaly_pairwise_completeness_higherOrderPrimitiveFactorCount
      r = 0 ∧
      Omega.Conclusion.conclusion_localized_anomaly_pairwise_completeness_certificateDimension r =
        Nat.choose r 2 := by
  constructor
  · rfl
  · simp [conclusion_localized_anomaly_pairwise_completeness_certificateDimension,
      conclusion_localized_anomaly_pairwise_completeness_pairIndex, Finset.card_powersetCard]

end Omega.Conclusion
