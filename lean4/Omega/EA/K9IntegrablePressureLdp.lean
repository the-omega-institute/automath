import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.EA.KernelOneSiteBernoulliClass

namespace Omega.EA

noncomputable section

/-- Paper label: `cor:k9-integrable-pressure-ldp`.
The `K9` pressure curve, its mean/variance densities in the `u = exp θ` parametrization, and the
binary-KL rate function are all explicit. -/
theorem paper_k9_integrable_pressure_ldp :
    K9_closed_form_pressure_curve ∧
      (∀ u : ℝ, 0 < u →
        k9Pressure (Real.log u) = Real.log (7 + 14 * u)) ∧
      (∀ u : ℝ, 0 < u →
        k9PressureDeriv (Real.log u) = 2 * u / (1 + 2 * u)) ∧
      (∀ u : ℝ, 0 < u →
        k9PressureVariance (Real.log u) = 2 * u / (1 + 2 * u) ^ 2) ∧
      K9_closed_form_rate_function := by
  rcases paper_kernel_one_site_bernoulli_class with ⟨_, hpressure, hrate⟩
  refine ⟨hpressure, ?_, ?_, ?_, hrate⟩
  · intro u hu
    simp [k9Pressure, Real.exp_log hu]
  · intro u hu
    simp [k9PressureDeriv, Real.exp_log hu]
  · intro u hu
    simp [k9PressureVariance, Real.exp_log hu]

end

end Omega.EA
