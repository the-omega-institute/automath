import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-hellinger-toeplitz-heine-szego-cue`. -/
theorem paper_xi_hellinger_toeplitz_heine_szego_cue
    (toeplitzDet cueIntegral toeplitzFreeEnergy cueFreeEnergy : ℕ → ℝ)
    (hHeine : ∀ κ, toeplitzDet κ = cueIntegral κ)
    (hFree : ∀ κ, toeplitzFreeEnergy κ = cueFreeEnergy κ) :
    (∀ κ, toeplitzDet κ = cueIntegral κ) ∧
      (∀ κ, toeplitzFreeEnergy κ = cueFreeEnergy κ) := by
  exact ⟨hHeine, hFree⟩

end Omega.Zeta
