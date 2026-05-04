import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-rh-critical-before-nearest-complex-branch`. -/
theorem paper_xi_rh_critical_before_nearest_complex_branch (thetaR Rtheta : ℝ)
    (analytic kernelRH : ℝ → Prop) (hcrit : thetaR < Rtheta)
    (hanalytic : ∀ θ, thetaR < θ → θ < Rtheta → analytic θ)
    (hrhFail : ∀ θ, thetaR < θ → θ < Rtheta → ¬ kernelRH θ) :
    thetaR < Rtheta ∧
      ∃ θ, thetaR < θ ∧ θ < Rtheta ∧ analytic θ ∧ ¬ kernelRH θ := by
  refine ⟨hcrit, ?_⟩
  let θ := (thetaR + Rtheta) / 2
  have hleft : thetaR < θ := by
    dsimp [θ]
    linarith
  have hright : θ < Rtheta := by
    dsimp [θ]
    linarith
  exact ⟨θ, hleft, hright, hanalytic θ hleft hright, hrhFail θ hleft hright⟩

end Omega.Zeta
