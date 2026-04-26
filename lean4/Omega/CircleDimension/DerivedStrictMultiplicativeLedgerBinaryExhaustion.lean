import Omega.CircleDimension.DerivedCofinalPrimeSupportUnboundedLedgerRank

namespace Omega.CircleDimension

/-- Paper label: `thm:derived-strict-multiplicative-ledger-binary-exhaustion`. -/
theorem paper_derived_strict_multiplicative_ledger_binary_exhaustion
    (D : DerivedCofinalPrimeSupportUnboundedLedgerRankData) :
    ((∃ C : ℕ, ∀ n, D.ledgerRank n ≤ C) → ¬ ∀ n, D.primeSupportSize n ≤ D.ledgerRank n) ∧
      ((∀ n, D.primeSupportSize n ≤ D.ledgerRank n) → ∀ C : ℕ, ∃ n, C < D.ledgerRank n) := by
  rcases paper_derived_cofinal_prime_support_unbounded_ledger_rank D with ⟨_, hunbounded⟩
  refine ⟨?_, ?_⟩
  · intro hbounded _
    rcases hbounded with ⟨C, hC⟩
    rcases hunbounded C with ⟨n, hn⟩
    exact Nat.not_lt_of_ge (hC n) hn
  · intro _
    exact hunbounded

end Omega.CircleDimension
