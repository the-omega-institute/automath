import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65ca-frozen-max-sector-oracle-capacity-lower-bound`. -/
theorem paper_xi_time_part65ca_frozen_max_sector_oracle_capacity_lower_bound
    (C K M P : ℕ → ℝ) (r : ℝ)
    (hlower : ∀ m, K m * min (M m) (P m) ≤ C m)
    (hsector : ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N →
      Real.exp ((r - ε) * (m : ℝ)) ≤ K m * min (M m) (P m)) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, m ≥ N →
      Real.exp ((r - ε) * (m : ℝ)) ≤ C m := by
  intro ε hε
  obtain ⟨N, hN⟩ := hsector ε hε
  refine ⟨N, ?_⟩
  intro m hm
  exact le_trans (hN m hm) (hlower m)

end Omega.Zeta
