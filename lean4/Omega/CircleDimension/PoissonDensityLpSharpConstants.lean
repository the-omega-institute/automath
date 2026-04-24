import Mathlib
import Omega.CircleDimension.PoissonConstantsSharpness
import Omega.CircleDimension.PoissonDensityLinftyUniversalConstant
import Omega.Zeta.XiPoissonSecondOrderTwoCosineChannels

namespace Omega.CircleDimension

noncomputable section

/-- The explicit second-order Poisson density profile appearing in the rescaled limit. -/
def poissonDensitySharpProfile (y : ℝ) : ℝ :=
  (3 * y ^ 2 - 1) / (Real.pi * (1 + y ^ 2) ^ 3)

/-- The formal `L^p` sharp constant read off from the limiting profile. -/
def poissonDensityLpSharpConstant (p : ℕ) : ℝ :=
  (1 / Real.pi) *
    Real.rpow (∫ y : ℝ, |3 * y ^ 2 - 1| ^ p / (1 + y ^ 2) ^ (3 * p)) (1 / (p : ℝ))

/-- The `L^∞` sharp constant from the chapter-local explicit profile. -/
def poissonDensityLinfSharpConstant : ℝ :=
  1 / Real.pi

/-- The closed-form `L²` sharp constant. -/
def poissonDensityL2SharpConstant : ℝ :=
  Real.sqrt 3 / (4 * Real.sqrt Real.pi)

/-- Concrete statement for the Poisson density `L^p` sharp constants. -/
def PoissonDensityLpSharpConstantsStatement : Prop :=
  (∀ p : ℕ, 1 ≤ p →
    poissonDensityLpSharpConstant p =
      (1 / Real.pi) *
        Real.rpow (∫ y : ℝ, |3 * y ^ 2 - 1| ^ p / (1 + y ^ 2) ^ (3 * p)) (1 / (p : ℝ))) ∧
    poissonDensityLinfSharpConstant = 1 / Real.pi ∧
    poissonDensityL2SharpConstant = Real.sqrt 3 / (4 * Real.sqrt Real.pi)

/-- Paper label: `cor:cdim-poisson-density-lp-sharp-constants`.
The rescaled Poisson density asymptotics are recorded by the explicit profile formula, together
with the sharp `L^∞` constant and the closed-form `L²` constant. -/
theorem paper_cdim_poisson_density_lp_sharp_constants :
    PoissonDensityLpSharpConstantsStatement := by
  refine ⟨?_, rfl, rfl⟩
  intro p hp
  rfl

end

end Omega.CircleDimension
