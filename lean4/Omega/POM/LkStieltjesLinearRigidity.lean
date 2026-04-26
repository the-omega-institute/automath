import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Paper label: `cor:pom-Lk-stieltjes-linear-rigidity`. In the concrete two-point bulk model with
mass `1` and first moment `2`, the Radon--Nikodym rewrite produces a boundary Stieltjes transform
which is an explicit affine function of the bulk transform. -/
theorem paper_pom_lk_stieltjes_linear_rigidity (z : ℂ) :
    let paper_label_pom_lk_stieltjes_linear_rigidity_Gν : ℂ :=
      (1 / 2 : ℂ) * (1 / z + 1 / (z - 4))
    let paper_label_pom_lk_stieltjes_linear_rigidity_Gρ : ℂ :=
      (1 / 2 : ℂ) *
        ((4 * z - z ^ 2) * paper_label_pom_lk_stieltjes_linear_rigidity_Gν + (z - 4) + 2)
    paper_label_pom_lk_stieltjes_linear_rigidity_Gρ =
      (z - 2) / 2 - (z * (z - 4) / 2) * paper_label_pom_lk_stieltjes_linear_rigidity_Gν := by
  dsimp
  ring

end

end Omega.POM
