import Omega.CircleDimension.PrimeLedgerCompleteReconstruction

namespace Omega.Zeta

/-- Paper label: `cor:xi-cdim-zeta-fingerprint-rigidity`.
In the circle-dimension model, the hom-count zeta fingerprint agrees with the finite-quotient
phase-spectrum profile, so equality of all layers forces equality of the free rank and the full
prime ledger. -/
theorem paper_xi_cdim_zeta_fingerprint_rigidity
    {r r' t t' : ℕ} (ht : 0 < t) (ht' : 0 < t')
    (hFingerprint : ∀ n : ℕ, 1 ≤ n →
      Omega.CircleDimension.phaseSpectrumCount r t n =
        Omega.CircleDimension.phaseSpectrumCount r' t' n) :
    r = r' ∧
      t = t' ∧
      Omega.CircleDimension.natPrimeLedger ⟨t, ht⟩ =
        Omega.CircleDimension.natPrimeLedger ⟨t', ht'⟩ ∧
      Omega.CircleDimension.natPrimeLedgerLift ⟨t, ht⟩ =
        Omega.CircleDimension.natPrimeLedgerLift ⟨t', ht'⟩ := by
  exact Omega.CircleDimension.paper_xi_cdim_prime_ledger_complete_reconstruction
    ht ht' hFingerprint

end Omega.Zeta
