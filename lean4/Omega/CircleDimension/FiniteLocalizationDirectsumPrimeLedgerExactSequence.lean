import Mathlib.Tactic
import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Witness package for a finite family of localizations together with its prime-ledger
    multiplicity profile and the discrete/compact exact sequences used in the paper statement.
    thm:cdim-finite-localization-directsum-prime-ledger-exact-sequence -/
structure FiniteLocalizationPrimeLedgerData where
  r : Nat
  primeSupport : Finset Nat
  m_p : Nat → Nat
  support_spec : ∀ p, p ∉ primeSupport → m_p p = 0
  primeSupport_nonempty : primeSupport.Nonempty
  discreteExactSequence : Prop
  compactExactSequence : Prop
  hDiscreteExactSequence : discreteExactSequence
  hCompactExactSequence : compactExactSequence
  rankBookkeeping : CircleDimHomData
  kernelRank_eq_zero : rankBookkeeping.kernelRank = 0
  imageRank_eq_r : rankBookkeeping.imageRank = r

/-- Paper-facing wrapper: a finite localization ledger carries its multiplicity profile, the
    discrete and compact exact-sequence packages, and the rank bookkeeping forces finite-rank
    circle dimension `r`.
    thm:cdim-finite-localization-directsum-prime-ledger-exact-sequence -/
theorem paper_cdim_finite_localization_directsum_prime_ledger_exact_sequence
    (L : FiniteLocalizationPrimeLedgerData) :
    ∃ m_p : Nat → Nat,
      (∀ p, p ∉ L.primeSupport → m_p p = 0) ∧
      L.discreteExactSequence ∧
      L.compactExactSequence ∧
      circleDim L.rankBookkeeping.sourceRank 0 = L.r := by
  refine ⟨L.m_p, L.support_spec, L.hDiscreteExactSequence, L.hCompactExactSequence, ?_⟩
  calc
    circleDim L.rankBookkeeping.sourceRank 0
        = circleDim L.rankBookkeeping.kernelRank 0 +
            circleDim L.rankBookkeeping.imageRank 0 := cdim_rank_nullity L.rankBookkeeping
    _ = 0 + L.r := by simp [L.kernelRank_eq_zero, L.imageRank_eq_r, circleDim]
    _ = L.r := by simp

end Omega.CircleDimension
