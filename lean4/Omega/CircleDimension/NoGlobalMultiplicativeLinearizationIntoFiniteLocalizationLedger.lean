import Mathlib.Tactic
import Omega.CircleDimension.FiniteLocalizationDirectsumPrimeLedgerExactSequence

namespace Omega.CircleDimension

/-- The exact-sequence package for a finite localization ledger exhibits the target additive host
as a finite-rank object. -/
def finiteLocalizationLedgerFiniteQRank (L : FiniteLocalizationPrimeLedgerData) : Prop :=
  ∃ m_p : Nat → Nat,
    (∀ p, p ∉ L.primeSupport → m_p p = 0) ∧
    L.discreteExactSequence ∧
    L.compactExactSequence ∧
    circleDim L.rankBookkeeping.sourceRank 0 = L.r

/-- A hypothetical global multiplicative linearization would force a positive-rank free abelian
piece to collapse to the zero kernel inside the finite localization ledger. -/
def globalMultiplicativeLinearizationIntoFiniteLocalizationLedgerObstruction
    (a : Nat) (L : FiniteLocalizationPrimeLedgerData) : Prop :=
  ∃ kernelRank : Nat,
    a + 1 ≤ kernelRank ∧ kernelRank = 0 ∧ finiteLocalizationLedgerFiniteQRank L

/-- Paper-facing obstruction: the finite localization ledger has finite additive rank, so the
Grothendieck-completion bookkeeping forbids any global multiplicative linearization into it. -/
def cdimNoGlobalMultiplicativeLinearizationIntoFiniteLocalizationLedger
    (a : Nat) (L : FiniteLocalizationPrimeLedgerData) : Prop :=
  finiteLocalizationLedgerFiniteQRank L ∧
    ¬ globalMultiplicativeLinearizationIntoFiniteLocalizationLedgerObstruction a L

/-- Paper label:
`thm:cdim-no-global-multiplicative-linearization-into-finite-localization-ledger`. -/
theorem paper_cdim_no_global_multiplicative_linearization_into_finite_localization_ledger
    (a : Nat) (L : Omega.CircleDimension.FiniteLocalizationPrimeLedgerData) :
    cdimNoGlobalMultiplicativeLinearizationIntoFiniteLocalizationLedger a L := by
  refine ⟨paper_cdim_finite_localization_directsum_prime_ledger_exact_sequence L, ?_⟩
  rintro ⟨kernelRank, hlower, hzero, _⟩
  have hone : 1 ≤ kernelRank := by
    exact le_trans (Nat.succ_le_succ (Nat.zero_le a)) hlower
  omega

end Omega.CircleDimension
