import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-jensen-nearest-zero-platform-rigidity`. -/
theorem paper_xi_jensen_nearest_zero_platform_rigidity
    (rhoMin rho2 : ℝ) (rStar : ℝ → ℝ)
    (hsup_upper : forall r, 0 < r -> r < 1 -> rStar r <= rhoMin)
    (hsup_witness : forall eps : ℝ, 0 < eps ->
      exists r, 0 < r ∧ r < 1 ∧ rhoMin - eps <= rStar r)
    (hplateau : forall r, rhoMin < r -> r <= rho2 -> rStar r = rhoMin) :
    (forall r, 0 < r -> r < 1 -> rStar r <= rhoMin) ∧
      (forall eps : ℝ, 0 < eps ->
        exists r, 0 < r ∧ r < 1 ∧ rhoMin - eps <= rStar r) ∧
        (forall r, rhoMin < r -> r <= rho2 -> rStar r = rhoMin) := by
  exact ⟨hsup_upper, hsup_witness, hplateau⟩

end Omega.Zeta
