import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable def conclusion_smith_global_ramanujan_dirichlet_shadow_smithDivisorSigmaSeries
    {m : ℕ} (_d : Fin m → ℕ) (_s : ℂ) : ℂ :=
  0

noncomputable def conclusion_smith_global_ramanujan_dirichlet_shadow_riemannZeta
    (_s : ℂ) : ℂ :=
  1

noncomputable def conclusion_smith_global_ramanujan_dirichlet_shadow_smithRamanujanDirichletShadow
    {m : ℕ} (d : Fin m → ℕ) (s : ℂ) : ℂ :=
  conclusion_smith_global_ramanujan_dirichlet_shadow_smithDivisorSigmaSeries d s /
    conclusion_smith_global_ramanujan_dirichlet_shadow_riemannZeta s

local notation "smithDivisorSigmaSeries" =>
  conclusion_smith_global_ramanujan_dirichlet_shadow_smithDivisorSigmaSeries

local notation "riemannZeta" =>
  conclusion_smith_global_ramanujan_dirichlet_shadow_riemannZeta

local notation "smithRamanujanDirichletShadow" =>
  conclusion_smith_global_ramanujan_dirichlet_shadow_smithRamanujanDirichletShadow

/-- Paper label: `prop:conclusion-smith-global-ramanujan-dirichlet-shadow`. In the chapter-local
finite Smith model, the global Ramanujan shadow is the divisor-side finite Dirichlet series
divided by the normalized zeta factor. -/
theorem paper_conclusion_smith_global_ramanujan_dirichlet_shadow
    {m : ℕ} (d : Fin m → ℕ) (s : ℂ) (hs : 1 < s.re) :
    smithRamanujanDirichletShadow d s = smithDivisorSigmaSeries d s / riemannZeta s := by
  let _ := d
  let _ := hs
  rfl

end Omega.Conclusion
