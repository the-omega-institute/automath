import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part61aca-primeweighted-mahalanobis-threshold-bernoulli-chain`. -/
theorem paper_xi_time_part61aca_primeweighted_mahalanobis_threshold_bernoulli_chain
    {r : ℕ} (q : Fin r → ℝ) (E : ℝ)
    (hmono : ∀ i j : Fin r, i ≤ j → q i ≤ q j) :
    ∃ J : Fin r → Prop, (∀ i, J i ↔ q i < E) ∧
      ∀ i j : Fin r, i ≤ j → J j → J i := by
  refine ⟨fun i => q i < E, ?_, ?_⟩
  · intro i
    rfl
  · intro i j hij hj
    exact lt_of_le_of_lt (hmono i j hij) hj

end Omega.Zeta
