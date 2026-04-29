import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9zq-natural-extension-infinite-primeslice-support`. -/
theorem paper_xi_time_part9zq_natural_extension_infinite_primeslice_support
    (activeSliceCount : Nat → Nat) :
    (∀ k, k ≤ activeSliceCount k) → ¬ ∃ N, ∀ k, activeSliceCount k ≤ N := by
  intro h_lower h_finite
  rcases h_finite with ⟨N, hN⟩
  exact Nat.not_succ_le_self N (le_trans (h_lower (N + 1)) (hN (N + 1)))

end Omega.Zeta
