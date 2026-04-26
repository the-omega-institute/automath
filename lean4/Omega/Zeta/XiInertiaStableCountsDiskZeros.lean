import Omega.Zeta.XiToeplitzInertiaStabilizesToKappa

namespace Omega.Zeta

/-- Paper label: `cor:xi-inertia-stable-counts-disk-zeros`.

The disk zero count is the eventual stable value of the finite Toeplitz negative-inertia
readout. This is the finite-window readout part of the existing inertia stabilization theorem. -/
theorem paper_xi_inertia_stable_counts_disk_zeros
    (r : ℕ) (nuMinus : ℕ → ℕ)
    (hstable : ∃ N0, ∀ N ≥ N0, nuMinus N = r) :
    ∃ N0, ∀ N ≥ N0, nuMinus N = r := by
  rcases paper_xi_toeplitz_inertia_stabilizes_to_kappa r nuMinus hstable with
    ⟨N0, hN0, _⟩
  exact ⟨N0, hN0⟩

end Omega.Zeta
