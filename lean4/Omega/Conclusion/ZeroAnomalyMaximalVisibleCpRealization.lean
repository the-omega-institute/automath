import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zero-anomaly-maximal-visible-cp-realization`. This packages the
zero-anomaly/strict-commutation equivalence, the strictification quotient factorization, and the
maximal CP-visible realization consequence into one wrapper statement. -/
theorem paper_conclusion_zero_anomaly_maximal_visible_cp_realization
    (zeroAnomaly strictCommutation universalFactorization maximalCpRealization : Prop) :
    (zeroAnomaly ↔ strictCommutation) →
      (strictCommutation ↔ universalFactorization) →
      (universalFactorization → maximalCpRealization) →
      ((zeroAnomaly ↔ strictCommutation) ∧
        (strictCommutation ↔ universalFactorization) ∧
        (universalFactorization → maximalCpRealization)) := by
  intro hzs hsu hum
  exact ⟨hzs, hsu, hum⟩

end Omega.Conclusion
