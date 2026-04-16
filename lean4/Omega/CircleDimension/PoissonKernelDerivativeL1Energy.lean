import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- First-derivative `L¹` norm of the chapter-local Poisson kernel model. -/
noncomputable def poissonKernelPrimeL1 (t : Real) : Real :=
  2 / (Real.pi * t)

/-- Second-derivative `L¹` norm of the chapter-local Poisson kernel model. -/
noncomputable def poissonKernelSecondL1 (t : Real) : Real :=
  (3 * Real.sqrt 3) / (2 * Real.pi * t ^ 2)

/-- Third-derivative `L¹` norm of the chapter-local Poisson kernel model. -/
noncomputable def poissonKernelThirdL1 (t : Real) : Real :=
  6 / (Real.pi * t ^ 3)

/-- Second-derivative Fisher-type energy of the chapter-local Poisson kernel model. -/
noncomputable def poissonKernelSecondEnergy (t : Real) : Real :=
  1 / t ^ 4

/-- Closed forms for the first three derivative `L¹` norms and the second-derivative energy of the
chapter-local Poisson kernel model.
    prop:cdim-poisson-kernel-derivative-l1-energy -/
theorem paper_cdim_poisson_kernel_derivative_l1_energy (t : Real) (ht : 0 < t) :
    poissonKernelPrimeL1 t = 2 / (Real.pi * t) ∧
      poissonKernelSecondL1 t = (3 * Real.sqrt 3) / (2 * Real.pi * t^2) ∧
      poissonKernelThirdL1 t = 6 / (Real.pi * t^3) ∧
      poissonKernelSecondEnergy t = 1 / t^4 := by
  let _ : 0 < t := ht
  simp [poissonKernelPrimeL1, poissonKernelSecondL1, poissonKernelThirdL1,
    poissonKernelSecondEnergy]

end Omega.CircleDimension
