import Mathlib.Tactic
import Omega.CircleDimension.PoissonKernelDerivativeL1Energy

namespace Omega.CircleDimension

/-- The symmetric two-point defect saturates the sharp second-order Poisson `L¹` and Fisher/KL
constants at `t = 1`.
    prop:cdim-poisson-constants-sharpness -/
theorem paper_cdim_poisson_constants_sharpness (a : ℝ) :
    ((a ^ 2) / 2) * poissonKernelSecondL1 1 = ((3 * Real.sqrt 3) / (4 * Real.pi)) * a ^ 2 ∧
      ((a ^ 4) / 8) * poissonKernelSecondEnergy 1 = a ^ 4 / 8 := by
  have hClosed := paper_cdim_poisson_kernel_derivative_l1_energy 1 zero_lt_one
  rcases hClosed with ⟨_, hSecondL1, _, hSecondEnergy⟩
  refine ⟨?_, ?_⟩
  · rw [hSecondL1]
    ring
  · rw [hSecondEnergy]
    ring

end Omega.CircleDimension
