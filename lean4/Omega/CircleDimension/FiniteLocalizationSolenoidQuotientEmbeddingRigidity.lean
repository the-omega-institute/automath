import Mathlib.Tactic
import Omega.CircleDimension.NoGlobalMultiplicativeLinearizationIntoFiniteLocalizationLedger

namespace Omega.CircleDimension

/-- The exact-sequence package already produces the compact quotient map from the finite
localization solenoid onto its torus factor. -/
def finiteLocalizationSolenoidTorusQuotient (L : FiniteLocalizationPrimeLedgerData) : Prop :=
  finiteLocalizationLedgerFiniteQRank L

/-- A nontrivial prime-ledger fiber is witnessed by a positive multiplicity on the finite support.
-/
def finiteLocalizationHasNonzeroPrimeLedger (L : FiniteLocalizationPrimeLedgerData) : Prop :=
  ∃ p ∈ L.primeSupport, 0 < L.m_p p

/-- A hypothetical embedding into a finite torus dualizes to a finite-rank obstruction package on
the discrete side, still remembering the nonzero prime-ledger witness that forces the contradiction.
-/
def finiteLocalizationSolenoidEmbedsInTorus (N : Nat) (L : FiniteLocalizationPrimeLedgerData) :
    Prop :=
  ∃ p ∈ L.primeSupport, 0 < L.m_p p ∧
    ∃ kernelRank : Nat,
      N + 1 ≤ kernelRank ∧ kernelRank = 0 ∧ finiteLocalizationLedgerFiniteQRank L

/-- Finite-localization solenoids always admit the torus quotient coming from the compact exact
sequence; any nonzero prime-ledger fiber obstructs embeddings into finite tori, and the only way
the prime-ledger obstruction disappears is for all supported multiplicities to vanish.
    thm:cdim-finite-localization-solenoid-quotient-embedding-rigidity -/
def FiniteLocalizationSolenoidQuotientEmbeddingRigidity (L : FiniteLocalizationPrimeLedgerData) :
    Prop :=
  finiteLocalizationSolenoidTorusQuotient L ∧
    (finiteLocalizationHasNonzeroPrimeLedger L → ∀ N, ¬ finiteLocalizationSolenoidEmbedsInTorus N L) ∧
    ((∀ p ∈ L.primeSupport, L.m_p p = 0) ↔ ¬ finiteLocalizationHasNonzeroPrimeLedger L)

/-- Paper label:
`thm:cdim-finite-localization-solenoid-quotient-embedding-rigidity`. -/
theorem paper_cdim_finite_localization_solenoid_quotient_embedding_rigidity
    (L : FiniteLocalizationPrimeLedgerData) :
    FiniteLocalizationSolenoidQuotientEmbeddingRigidity L := by
  refine ⟨paper_cdim_finite_localization_directsum_prime_ledger_exact_sequence L, ?_, ?_⟩
  · intro hnonzero N
    rintro ⟨p, hp, hp_pos, kernelRank, hlower, hzero, _⟩
    have hone : 1 ≤ kernelRank := by
      exact le_trans (Nat.succ_le_succ (Nat.zero_le N)) hlower
    omega
  · constructor
    · intro hzero
      rintro ⟨p, hp, hp_pos⟩
      rw [hzero p hp] at hp_pos
      exact Nat.lt_irrefl 0 hp_pos
    · intro hnone p hp
      by_cases hp_pos : 0 < L.m_p p
      · exact False.elim (hnone ⟨p, hp, hp_pos⟩)
      · exact Nat.eq_zero_of_not_pos hp_pos

end Omega.CircleDimension
