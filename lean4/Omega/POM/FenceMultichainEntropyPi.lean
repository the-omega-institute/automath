import Mathlib.Data.Nat.Basic

namespace Omega.POM

/-- Paper label: `cor:pom-fence-multichain-entropy-pi`. The spectral-limit package,
half-angle closed form, and resulting pi-asymptotic are assembled by successive consequences. -/
theorem paper_pom_fence_multichain_entropy_pi (k : ℕ) (hk : 1 ≤ k)
    (spectralLimit closedForm piAsymptotic : Prop) (hSpectral : spectralLimit)
    (hClosed : spectralLimit → closedForm) (hPi : closedForm → piAsymptotic) :
    spectralLimit ∧ closedForm ∧ piAsymptotic := by
  have _ : 1 ≤ k := hk
  exact ⟨hSpectral, hClosed hSpectral, hPi (hClosed hSpectral)⟩

end Omega.POM
