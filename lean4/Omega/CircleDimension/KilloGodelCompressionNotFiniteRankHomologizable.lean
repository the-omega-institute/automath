import Mathlib.Tactic
import Omega.CircleDimension.DerivedCofinalPrimeSupportUnboundedLedgerRank

namespace Omega.CircleDimension

/-- Concrete Killo-Godel ledger data: the multiplicative prime support appearing at stage `n`
and a single finite ambient additive rank proposed for a faithful homologization. -/
structure KilloGodelLedgerData where
  primeSupportSize : ℕ → ℕ
  finiteHostRank : ℕ
  cofinalPrimeSupport : ∀ C, ∃ n, C < primeSupportSize n

namespace KilloGodelLedgerData

/-- A faithful additive homologization would assign each stage a ledger rank bounded below by the
visible prime support and uniformly bounded above by one fixed finite host rank. -/
def FaithfulHomologizable (D : KilloGodelLedgerData) : Prop :=
  ∃ ledgerRank : ℕ → ℕ,
    (∀ n, D.primeSupportSize n ≤ ledgerRank n) ∧
      (∀ n, ledgerRank n ≤ D.finiteHostRank)

end KilloGodelLedgerData

open KilloGodelLedgerData

/-- Paper label: `thm:killo-godel-compression-not-finite-rank-homologizable`. A faithful
finite-rank additive host would force the stagewise ledger ranks to be simultaneously unbounded by
cofinal prime support and bounded by the host rank, which is impossible. -/
theorem paper_killo_godel_compression_not_finite_rank_homologizable
    (D : KilloGodelLedgerData) : ¬ D.FaithfulHomologizable := by
  rintro ⟨ledgerRank, hlower, hupper⟩
  let E : DerivedCofinalPrimeSupportUnboundedLedgerRankData :=
    { primeSupportSize := D.primeSupportSize
      ledgerRank := ledgerRank
      cofinalPrimeSupport := D.cofinalPrimeSupport
      stagewiseLowerBound := hlower }
  have hunbounded := paper_derived_cofinal_prime_support_unbounded_ledger_rank E
  rcases hunbounded.2 D.finiteHostRank with ⟨n, hn⟩
  exact Nat.not_lt_of_ge (hupper n) hn

end Omega.CircleDimension
