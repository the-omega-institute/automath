import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part60e-truncated-jensen-profile-completeness-blindness`. -/
theorem paper_xi_time_part60e_truncated_jensen_profile_completeness_blindness
    (uStar : ℝ) (visible : List ℝ → List ℝ) (profile : List ℝ → ℝ → ℝ)
    (hprofile : ∀ zs u, u ≤ uStar → profile zs u = profile (visible zs) u)
    (hinvisible : ∀ zs extra, visible (zs ++ extra) = visible zs) {F G : List ℝ}
    (hvis : visible F = visible G) :
    (∀ u, u ≤ uStar → profile F u = profile G u) ∧
      (∀ extra u, u ≤ uStar → profile (F ++ extra) u = profile F u) := by
  constructor
  · intro u hu
    calc
      profile F u = profile (visible F) u := hprofile F u hu
      _ = profile (visible G) u := by rw [hvis]
      _ = profile G u := by rw [hprofile G u hu]
  · intro extra u hu
    calc
      profile (F ++ extra) u = profile (visible (F ++ extra)) u := hprofile (F ++ extra) u hu
      _ = profile (visible F) u := by rw [hinvisible F extra]
      _ = profile F u := by rw [hprofile F u hu]

end Omega.Zeta
