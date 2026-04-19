import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Stagewise prime-support sizes and ledger ranks for the cofinal-growth contradiction. -/
structure DerivedCofinalPrimeSupportUnboundedLedgerRankData where
  primeSupportSize : ℕ → ℕ
  ledgerRank : ℕ → ℕ
  cofinalPrimeSupport : ∀ C, ∃ n, C < primeSupportSize n
  stagewiseLowerBound : ∀ n, primeSupportSize n ≤ ledgerRank n

/-- Cofinal prime-support growth forces unbounded ledger rank because every stagewise faithful
ledger must have rank at least the number of supported prime directions.
    thm:derived-cofinal-prime-support-unbounded-ledger-rank -/
theorem paper_derived_cofinal_prime_support_unbounded_ledger_rank
    (D : DerivedCofinalPrimeSupportUnboundedLedgerRankData) :
    (forall n, D.primeSupportSize n <= D.ledgerRank n) ∧
      (forall C, exists n, C < D.ledgerRank n) := by
  refine ⟨D.stagewiseLowerBound, ?_⟩
  intro C
  rcases D.cofinalPrimeSupport C with ⟨n, hn⟩
  refine ⟨n, lt_of_lt_of_le hn (D.stagewiseLowerBound n)⟩

end Omega.CircleDimension
