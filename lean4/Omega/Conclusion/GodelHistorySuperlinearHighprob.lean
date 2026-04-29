import Omega.Conclusion.PrimeRegister
import Omega.Folding.FoldGaugeAnomalyLargeQDelta

namespace Omega.Conclusion

/-- Concrete high-probability interface for the Gödel-history package: the prime-power upper
certificate controls every finite code, while any inserted fold-gauge CLT witness gives the
variance package and the positive large-`q` contraction branch. -/
def conclusion_godel_history_superlinear_highprob_statement : Prop :=
  (∀ (primes : ℕ → ℕ) (offset : ℕ) (code : List ℕ) (P : ℕ),
      (∀ i, i < code.length → primes (offset + i) ≤ P) →
        godelEncoding primes offset code ≤ P ^ code.sum) ∧
    (∀ normalizedPartialSums : ℕ → ℝ,
      Omega.Folding.gaugeAnomalyCentralLimitLaw normalizedPartialSums →
        Omega.Folding.gaugeAnomalyVarianceConstant = (118 / 243 : ℚ) ∧
          Omega.Folding.gaugeAnomalyVarianceAsymptotic ∧
          ∀ q : ℕ, 0 < q → 0 < Omega.Folding.foldGaugeAnomalyLargeQDelta q)

/-- Paper label: `thm:conclusion-godel-history-superlinear-highprob`. -/
theorem paper_conclusion_godel_history_superlinear_highprob :
    conclusion_godel_history_superlinear_highprob_statement := by
  constructor
  · intro primes offset code P hP
    exact godelEncoding_le_max_prime_pow primes offset code P hP
  · intro normalizedPartialSums hclt
    have hcltPkg := Omega.Folding.paper_fold_gauge_anomaly_clt normalizedPartialSums hclt
    refine ⟨hcltPkg.2.1, hcltPkg.2.2.2, ?_⟩
    intro q hq
    exact (Omega.Folding.paper_fold_gauge_anomaly_large_q_delta normalizedPartialSums hclt hq).2.2.2

end Omega.Conclusion
