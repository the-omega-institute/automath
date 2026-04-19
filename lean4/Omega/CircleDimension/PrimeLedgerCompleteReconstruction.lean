import Omega.CircleDimension.CircleDim
import Omega.CircleDimension.PrimeTruncation

namespace Omega.CircleDimension

/-- Paper-facing reconstruction package for the phase-spectrum prime ledger.
    The full phase spectrum recovers the free rank, the torsion parameter, and therefore the
    complete prime ledger of the torsion part.
    thm:xi-cdim-prime-ledger-complete-reconstruction -/
theorem paper_xi_cdim_prime_ledger_complete_reconstruction
    {r r' t t' : ℕ} (ht : 0 < t) (ht' : 0 < t')
    (hSpectrum : ∀ N : ℕ, 1 ≤ N → phaseSpectrumCount r t N = phaseSpectrumCount r' t' N) :
    r = r' ∧
      t = t' ∧
      natPrimeLedger ⟨t, ht⟩ = natPrimeLedger ⟨t', ht'⟩ ∧
      natPrimeLedgerLift ⟨t, ht⟩ = natPrimeLedgerLift ⟨t', ht'⟩ := by
  rcases phaseSpectrumCount_reconstruction ht ht' hSpectrum with ⟨hr, htEq⟩
  subst htEq
  refine ⟨hr, rfl, rfl, rfl⟩

end Omega.CircleDimension
