import Mathlib.Tactic
import Omega.CircleDimension.DerivedCofinalPrimeSupportUnboundedLedgerRank

namespace Omega.Conclusion

/-- Concrete finite-stage ledger data for the global anomaly/rank dichotomy. -/
structure conclusion_global_ledger_anomaly_rank_divergence_dichotomy_data where
  conclusion_global_ledger_anomaly_rank_divergence_dichotomy_strictHomAt : ℕ → Bool
  conclusion_global_ledger_anomaly_rank_divergence_dichotomy_primeSupportSize : ℕ → ℕ
  conclusion_global_ledger_anomaly_rank_divergence_dichotomy_ledgerRank : ℕ → ℕ
  conclusion_global_ledger_anomaly_rank_divergence_dichotomy_cofinalPrimeSupport :
    ∀ C, ∃ n,
      C <
        conclusion_global_ledger_anomaly_rank_divergence_dichotomy_primeSupportSize n
  conclusion_global_ledger_anomaly_rank_divergence_dichotomy_rankLowerBound_of_strict :
    ∀ n,
      conclusion_global_ledger_anomaly_rank_divergence_dichotomy_strictHomAt n = true →
        conclusion_global_ledger_anomaly_rank_divergence_dichotomy_primeSupportSize n ≤
          conclusion_global_ledger_anomaly_rank_divergence_dichotomy_ledgerRank n

/-- The ledger ranks are unbounded along finite stages. -/
def conclusion_global_ledger_anomaly_rank_divergence_dichotomy_rankDiverges
    (D : conclusion_global_ledger_anomaly_rank_divergence_dichotomy_data) : Prop :=
  ∀ C, ∃ n, C < D.conclusion_global_ledger_anomaly_rank_divergence_dichotomy_ledgerRank n

/-- Strict homomorphism already fails at a finite stage. -/
def conclusion_global_ledger_anomaly_rank_divergence_dichotomy_finiteStageFailure
    (D : conclusion_global_ledger_anomaly_rank_divergence_dichotomy_data) : Prop :=
  ∃ n, D.conclusion_global_ledger_anomaly_rank_divergence_dichotomy_strictHomAt n = false

/-- Either strict homomorphism persists and ranks diverge, or strictness fails finitely. -/
def conclusion_global_ledger_anomaly_rank_divergence_dichotomy_statement
    (D : conclusion_global_ledger_anomaly_rank_divergence_dichotomy_data) : Prop :=
  conclusion_global_ledger_anomaly_rank_divergence_dichotomy_rankDiverges D ∨
    conclusion_global_ledger_anomaly_rank_divergence_dichotomy_finiteStageFailure D

/-- Paper label: `cor:conclusion-global-ledger-anomaly-rank-divergence-dichotomy`. -/
theorem paper_conclusion_global_ledger_anomaly_rank_divergence_dichotomy
    (D : conclusion_global_ledger_anomaly_rank_divergence_dichotomy_data) :
    conclusion_global_ledger_anomaly_rank_divergence_dichotomy_statement D := by
  by_cases hstrict :
      ∀ n, D.conclusion_global_ledger_anomaly_rank_divergence_dichotomy_strictHomAt n = true
  · left
    let E : Omega.CircleDimension.DerivedCofinalPrimeSupportUnboundedLedgerRankData :=
      { primeSupportSize :=
          D.conclusion_global_ledger_anomaly_rank_divergence_dichotomy_primeSupportSize
        ledgerRank :=
          D.conclusion_global_ledger_anomaly_rank_divergence_dichotomy_ledgerRank
        cofinalPrimeSupport :=
          D.conclusion_global_ledger_anomaly_rank_divergence_dichotomy_cofinalPrimeSupport
        stagewiseLowerBound := fun n =>
          D.conclusion_global_ledger_anomaly_rank_divergence_dichotomy_rankLowerBound_of_strict
            n (hstrict n) }
    exact (Omega.CircleDimension.paper_derived_cofinal_prime_support_unbounded_ledger_rank E).2
  · right
    by_contra hnone
    apply hstrict
    intro n
    cases htag :
        D.conclusion_global_ledger_anomaly_rank_divergence_dichotomy_strictHomAt n with
    | false =>
        exact False.elim (hnone ⟨n, htag⟩)
    | true =>
        rfl

end Omega.Conclusion
