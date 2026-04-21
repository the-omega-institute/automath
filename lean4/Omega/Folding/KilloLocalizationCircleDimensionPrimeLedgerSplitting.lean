import Omega.CircleDimension.FiniteLocalizationDirectsumPrimeLedgerExactSequence
import Omega.Zeta.LocalizedIntegersPadicKernelRigidity

namespace Omega.Folding

/-- Paper-facing package that combines the finite-localization exact-sequence ledger with the
localized-integers `p`-adic kernel rigidity package.
    thm:killo-localization-circle-dimension-prime-ledger-splitting -/
theorem paper_killo_localization_circle_dimension_prime_ledger_splitting
    (L : Omega.CircleDimension.FiniteLocalizationPrimeLedgerData) (hL : L.r = 1)
    (D : Omega.Zeta.LocalizedIntegersPadicKernelRigidityData) :
    (∃ m_p : Nat → Nat,
      (∀ p, p ∉ L.primeSupport → m_p p = 0) ∧
      L.discreteExactSequence ∧
      L.compactExactSequence ∧
      Omega.CircleDimension.circleDim L.rankBookkeeping.sourceRank 0 = 1) ∧
      D.shortExactSequence ∧
      D.connectedComponentIsCircle ∧
      D.circleDimensionOne ∧
      D.padicKernelRecoversPrimeSet := by
  rcases
      Omega.CircleDimension.paper_cdim_finite_localization_directsum_prime_ledger_exact_sequence L
    with ⟨m_p, hm_p, hDiscrete, hCompact, hCircle⟩
  refine ⟨?_, D.shortExactSequenceWitness, D.connectedComponentWitness, D.circleDimensionWitness,
    D.primeSetRecoveryWitness⟩
  refine ⟨m_p, hm_p, hDiscrete, hCompact, ?_⟩
  simpa [hL] using hCircle

end Omega.Folding
