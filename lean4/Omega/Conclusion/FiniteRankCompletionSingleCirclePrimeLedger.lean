import Omega.Folding.KilloLocalizationCircleDimensionPrimeLedgerSplitting

namespace Omega.Conclusion

/-- Conclusion-level rank-one restatement of the finite-localization prime ledger completion:
the splitting theorem already supplies the finite ledger and the localized-integers package
supplies the `p`-adic kernel recovery data.
    cor:conclusion-finite-rank-completion-single-circle-prime-ledger -/
theorem paper_conclusion_finite_rank_completion_single_circle_prime_ledger
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
  exact Omega.Folding.paper_killo_localization_circle_dimension_prime_ledger_splitting L hL D

end Omega.Conclusion
