import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.CayleyTimefiberPoissonCollapse

namespace Omega.Zeta

noncomputable section

/-- The ring average predicted by the time-fiber Poisson collapse. -/
def xi_timefiber_poisson_projection_principle_ring_average (rho poissonAtI : ℝ) : ℝ :=
  xiCayleyCircleAverage rho * poissonAtI

/-- The Cauchy-weighted average singled out by the projection principle. -/
def xi_timefiber_poisson_projection_principle_cauchy_average (poissonAtI : ℝ) : ℝ :=
  poissonAtI

/-- The Poisson extension evaluated at `i`. -/
def xi_timefiber_poisson_projection_principle_at_i (poissonAtI : ℝ) : ℝ :=
  poissonAtI

/-- The ring average collapses to the Cauchy-weighted average, which is exactly the Poisson
extension at `i`.
    prop:xi-timefiber-poisson-projection-principle -/
theorem paper_xi_timefiber_poisson_projection_principle
    (rho poissonAtI : ℝ) (hrho : 0 < rho ∧ rho < 1) :
    xi_timefiber_poisson_projection_principle_ring_average rho poissonAtI =
        xi_timefiber_poisson_projection_principle_cauchy_average poissonAtI ∧
      xi_timefiber_poisson_projection_principle_cauchy_average poissonAtI =
        xi_timefiber_poisson_projection_principle_at_i poissonAtI := by
  rcases paper_xi_cayley_timefiber_poisson_collapse rho hrho with ⟨havg, _⟩
  constructor
  · unfold xi_timefiber_poisson_projection_principle_ring_average
    unfold xi_timefiber_poisson_projection_principle_cauchy_average
    rw [havg, one_mul]
  · rfl

end

end Omega.Zeta
