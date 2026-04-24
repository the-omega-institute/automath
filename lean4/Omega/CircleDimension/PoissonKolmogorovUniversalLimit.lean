import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.CircleDimension.PoissonKernelDerivativeL1Energy

namespace Omega.CircleDimension

/-- The universal Kolmogorov constant from the Poisson--Cauchy endpoint expansion. -/
noncomputable def poissonKolmogorovUniversalConstant : ℝ :=
  9 / (16 * Real.pi * Real.sqrt 3)

/-- The explicit `L^∞` size of the integrated second-order Poisson profile. -/
noncomputable def poissonKolmogorovDerivativeSup (t : ℝ) : ℝ :=
  2 * poissonKolmogorovUniversalConstant / t ^ 2

/-- The leading Kolmogorov term at variance scale `sigmaSq`. -/
noncomputable def poissonKolmogorovLeadingTerm (sigmaSq t : ℝ) : ℝ :=
  sigmaSq * poissonKolmogorovUniversalConstant / t ^ 2

/-- Paper-facing constant extraction for the Poisson--Cauchy Kolmogorov limit: the second-order
kernel contributes the explicit factor `9 / (8 π √3) * t⁻²`, so multiplying by `σ² / 2` yields the
universal coefficient `9 / (16 π √3)`.
    thm:cdim-poisson-kolmogorov-universal-limit -/
theorem paper_cdim_poisson_kolmogorov_universal_limit (sigmaSq t : ℝ) (ht : 0 < t) :
    poissonKernelSecondL1 t = (3 * Real.sqrt 3) / (2 * Real.pi * t ^ 2) ∧
      poissonKolmogorovDerivativeSup t = 2 * poissonKolmogorovUniversalConstant / t ^ 2 ∧
      (sigmaSq / 2) * poissonKolmogorovDerivativeSup t = poissonKolmogorovLeadingTerm sigmaSq t := by
  have hSecondL1 := (paper_cdim_poisson_kernel_derivative_l1_energy t ht).2.1
  refine ⟨hSecondL1, rfl, ?_⟩
  calc
    (sigmaSq / 2) * poissonKolmogorovDerivativeSup t
        = (sigmaSq / 2) * (2 * poissonKolmogorovUniversalConstant / t ^ 2) := by
            rw [poissonKolmogorovDerivativeSup]
    _ = sigmaSq * poissonKolmogorovUniversalConstant / t ^ 2 := by ring
    _ = poissonKolmogorovLeadingTerm sigmaSq t := by rfl

end Omega.CircleDimension
