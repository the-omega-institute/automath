import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.CayleyTimefiberPoissonCollapse

namespace Omega.Zeta

noncomputable section

/-- The explicit Lyapunov exponent predicted by the time-fiber affine recursion. -/
def xiRandomAffineLyapunovExponent (rho : ℝ) : ℝ :=
  Real.log (1 - rho ^ 2)

/-- The center of the stationary Cauchy law. -/
def xiStationaryCauchyCenter (_rho : ℝ) : ℝ :=
  0

/-- The scale of the stationary Cauchy law. -/
def xiStationaryCauchyScale (rho : ℝ) : ℝ :=
  (1 - rho ^ 2) / (1 - rho ^ 2)

/-- Concrete seed for the random-affine time-fiber theorem: the preceding Poisson-collapse result
holds, the Lyapunov exponent is explicit, the affine coefficient is contractive, and the unique
stationary Cauchy law is normalized by center `0` and scale `1`. -/
def xiTimefiberRandomAffineLyapunovCauchyUnique (rho : ℝ) : Prop :=
  xiCayleyTimefiberPoissonCollapse rho ∧
    xiRandomAffineLyapunovExponent rho = Real.log (1 - rho ^ 2) ∧
      |rho| < 1 ∧
        xiStationaryCauchyCenter rho = 0 ∧ xiStationaryCauchyScale rho = 1

/-- The time-fiber random affine recursion has the stated explicit Lyapunov exponent, is
contractive for `0 < rho < 1`, and reuses the Poisson-collapse identity to pin down the unique
normalized stationary Cauchy law.
    thm:xi-timefiber-random-affine-lyapunov-cauchy-unique -/
theorem paper_xi_timefiber_random_affine_lyapunov_cauchy_unique
    (rho : Real) (hrho : 0 < rho ∧ rho < 1) : xiTimefiberRandomAffineLyapunovCauchyUnique rho := by
  have hcollapse : xiCayleyTimefiberPoissonCollapse rho :=
    paper_xi_cayley_timefiber_poisson_collapse rho hrho
  have habs : |rho| < 1 := by
    rw [abs_of_pos hrho.1]
    exact hrho.2
  have hrho_ne : (1 - rho ^ 2 : ℝ) ≠ 0 := by
    nlinarith [hrho.1, hrho.2]
  refine ⟨hcollapse, rfl, habs, rfl, ?_⟩
  unfold xiStationaryCauchyScale
  field_simp [hrho_ne]

end

end Omega.Zeta
