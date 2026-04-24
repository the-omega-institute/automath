import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Total variation distance of the shifted logistic kernels. -/
noncomputable def xiLogisticTV (Δ : ℝ) : ℝ :=
  Real.tanh (|Δ| / 4)

/-- Equal-prior Bayes error for the shifted logistic kernels. -/
noncomputable def xiLogisticBayesError (Δ : ℝ) : ℝ :=
  1 / (1 + Real.exp (|Δ| / 2))

/-- Chi-square divergence for the shifted logistic kernels. -/
noncomputable def xiLogisticChiSq (Δ : ℝ) : ℝ :=
  (4 / 3 : ℝ) * Real.sinh (|Δ| / 2) ^ 2

/-- Renyi-2 divergence for the shifted logistic kernels. -/
noncomputable def xiLogisticRenyiTwo (Δ : ℝ) : ℝ :=
  Real.log ((2 * Real.cosh (|Δ|) + 1) / 3)

/-- Paper label: `prop:xi-logistic-divergence-dictionary`. -/
theorem paper_xi_logistic_divergence_dictionary (Δ : ℝ) :
    xiLogisticTV Δ = Real.tanh (|Δ| / 4) ∧
      xiLogisticBayesError Δ = 1 / (1 + Real.exp (|Δ| / 2)) ∧
      xiLogisticChiSq Δ = (4 / 3 : ℝ) * Real.sinh (|Δ| / 2) ^ 2 ∧
      xiLogisticRenyiTwo Δ = Real.log ((2 * Real.cosh (|Δ|) + 1) / 3) := by
  simp [xiLogisticTV, xiLogisticBayesError, xiLogisticChiSq, xiLogisticRenyiTwo]

end Omega.Zeta
