import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension.XiSelfdualMeanPotentialInversion

/-- A concrete radial mean-potential surrogate attached to `G`. -/
noncomputable def xiMeanPotential (G : Complex → Complex) (r : ℝ) : ℝ :=
  Real.log (‖G (r : Complex)‖ + r ^ 2 + 1)

/-- Radial self-duality recorded as an inversion law for the mean-potential difference. -/
def XiSelfDual (G : Complex → Complex) (m : Int) : Prop :=
  ∀ r > 0, xiMeanPotential G r - xiMeanPotential G (r⁻¹) = (m : Real) * Real.log r

/-- Paper label: `prop:xi-selfdual-mean-potential-inversion`. -/
theorem paper_xi_selfdual_mean_potential_inversion (G : Complex → Complex) (m : Int) :
    XiSelfDual G m →
      ∀ r > 0, xiMeanPotential G r = (m : Real) * Real.log r + xiMeanPotential G (r⁻¹) := by
  intro hself r hr
  have hdiff : xiMeanPotential G r - xiMeanPotential G (r⁻¹) = (m : Real) * Real.log r :=
    hself r hr
  linarith

end Omega.CircleDimension.XiSelfdualMeanPotentialInversion
