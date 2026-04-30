import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9s-resonance-entire-integer-sampling-not-l2`. -/
theorem paper_xi_time_part9s_resonance_entire_integer_sampling_not_l2 (F C : ℤ → ℝ)
    (squareSummable : (ℤ → ℝ) → Prop)
    (hsquare_congr : ∀ f g : ℤ → ℝ, (∀ n, |f n| = |g n|) →
      (squareSummable f ↔ squareSummable g))
    (habs : ∀ n, |F n| = |C n|) (hC : ¬ squareSummable C) : ¬ squareSummable F := by
  intro hF
  exact hC ((hsquare_congr F C habs).mp hF)

end Omega.Zeta
