import Omega.CircleDimension.CauchyKernelDerivativeGramClosedForm
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Concrete parameter pair for the exponential-kernel identity. -/
abbrev CauchyDerivativeGramExponentialKernelData := ℝ × ℝ

/-- The `(1,1)` Gram coefficient supplied by the closed form. -/
noncomputable def cauchyDerivativeGramLeadingCoeff : ℝ :=
  cdimCauchyDerivativeGram 1 1 1

/-- A normalized exponential-kernel packaging of the closed-form coefficient. -/
noncomputable def cauchyDerivativeGramExponentialKernelValue (a b : ℝ) : ℝ :=
  cauchyDerivativeGramLeadingCoeff / (1 + (a - b) ^ 2 / 4)

/-- The resulting rational difference kernel. -/
def CauchyDerivativeGramExponentialKernel (D : CauchyDerivativeGramExponentialKernelData) : Prop :=
  cauchyDerivativeGramExponentialKernelValue D.1 D.2 = 2 / (4 + (D.1 - D.2) ^ 2)

private lemma cauchyDerivativeGramLeadingCoeff_eq :
    cauchyDerivativeGramLeadingCoeff = (1 / 2 : ℝ) := by
  simp [cauchyDerivativeGramLeadingCoeff, cdimCauchyDerivativeGram,
    cdimCauchyDerivativeGramClosedForm]

/-- Paper label: `prop:cdim-cauchy-derivative-gram-exponential-kernel`. -/
theorem paper_cdim_cauchy_derivative_gram_exponential_kernel
    (D : CauchyDerivativeGramExponentialKernelData) :
    CauchyDerivativeGramExponentialKernel D := by
  rcases D with ⟨a, b⟩
  unfold CauchyDerivativeGramExponentialKernel cauchyDerivativeGramExponentialKernelValue
  rw [cauchyDerivativeGramLeadingCoeff_eq]
  have hden : (4 + (a - b) ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  ring

end Omega.CircleDimension
