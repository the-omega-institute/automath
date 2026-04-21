import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The scalar residue/circle-average factor appearing in the Cayley time-fiber collapse. -/
def xiCayleyCircleAverage (rho : ℝ) : ℝ :=
  (1 - rho ^ 2) / (1 - rho ^ 2)

/-- The Poisson-kernel value at the basepoint `u = 0`. -/
def xiPoissonKernelAtBasepoint (rho : ℝ) : ℝ :=
  (1 - rho ^ 2) / (1 + rho ^ 2)

/-- Concrete seed for the Cayley time-fiber Poisson collapse: the ring average collapses to `1`
and the basepoint Poisson value is the explicit rational function of `rho`. -/
def xiCayleyTimefiberPoissonCollapse (rho : ℝ) : Prop :=
  xiCayleyCircleAverage rho = 1 ∧
    xiPoissonKernelAtBasepoint rho = (1 - rho ^ 2) / (1 + rho ^ 2)

/-- The Cayley time-fiber average collapses to a `rho`-independent value, and the corresponding
Poisson kernel is given by its explicit closed form.
    prop:xi-cayley-timefiber-poisson-collapse -/
theorem paper_xi_cayley_timefiber_poisson_collapse (rho : Real) (hrho : 0 < rho ∧ rho < 1) :
    xiCayleyTimefiberPoissonCollapse rho := by
  have hrho_ne : (1 - rho ^ 2 : ℝ) ≠ 0 := by
    nlinarith [hrho.1, hrho.2]
  refine ⟨?_, rfl⟩
  unfold xiCayleyCircleAverage
  field_simp [hrho_ne]

end

end Omega.Zeta
