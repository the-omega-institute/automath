import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-oracle-sigma-determines-tau-on-01`. The restricted Fenchel inverse
data on `[-1,0]` determines `tau` on `[0,1]` by substituting `theta = q - 1`. -/
theorem paper_pom_oracle_sigma_determines_tau_on_01
    (tau₁ tau₂ Lambda₁ Lambda₂ : ℝ → ℝ)
    (hTau₁ : tau₁ 1 = Real.log 2)
    (hTau₂ : tau₂ 1 = Real.log 2)
    (hLambda₁ : ∀ q ∈ Set.Icc (0 : ℝ) 1, Lambda₁ (q - 1) = tau₁ q - tau₁ 1)
    (hLambda₂ : ∀ q ∈ Set.Icc (0 : ℝ) 1, Lambda₂ (q - 1) = tau₂ q - tau₂ 1)
    (hSame : ∀ θ ∈ Set.Icc (-1 : ℝ) 0, Lambda₁ θ = Lambda₂ θ) :
    ∀ q ∈ Set.Icc (0 : ℝ) 1, tau₁ q = tau₂ q := by
  intro q hq
  have htheta : q - 1 ∈ Set.Icc (-1 : ℝ) 0 := by
    constructor <;> linarith [hq.1, hq.2]
  have h₁ := hLambda₁ q hq
  have h₂ := hLambda₂ q hq
  have hsame := hSame (q - 1) htheta
  rw [h₁, h₂, hTau₁, hTau₂] at hsame
  linarith

end Omega.POM
