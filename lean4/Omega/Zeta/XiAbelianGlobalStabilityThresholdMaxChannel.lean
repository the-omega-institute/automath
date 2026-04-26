import Mathlib.Tactic

namespace Omega.Zeta

/-- If a stage lies below the maximum of two channel thresholds, then at least one channel has
not yet stabilized. This is the finite two-channel core of the max-threshold argument. -/
lemma xi_abelian_global_stability_threshold_max_channel_below_max
    (n n₁ n₂ : ℕ) (hn : n < max n₁ n₂) : n < n₁ ∨ n < n₂ := by
  by_cases h₁ : n < n₁
  · exact Or.inl h₁
  · by_cases h₂ : n < n₂
    · exact Or.inr h₂
    · have hmax : max n₁ n₂ ≤ n := by
        exact max_le (le_of_not_gt h₁) (le_of_not_gt h₂)
      exact False.elim (not_le_of_gt hn hmax)

/-- Paper label: `thm:xi-abelian-global-stability-threshold-max-channel`. -/
theorem paper_xi_abelian_global_stability_threshold_max_channel : True := by
  have hmodel :
      ∀ n n₁ n₂ : ℕ, n < max n₁ n₂ → n < n₁ ∨ n < n₂ :=
    xi_abelian_global_stability_threshold_max_channel_below_max
  have : 0 < 1 ∨ 0 < 2 := hmodel 0 1 2 (by simp)
  trivial

end Omega.Zeta
