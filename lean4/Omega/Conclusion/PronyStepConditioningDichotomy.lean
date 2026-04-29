import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.Conclusion.StieltjesPronyStepOptimalLaw

namespace Omega.Conclusion

/-- The exponential side of the dichotomy: once `tΔ ≥ 1`, the model separation factor is
bounded by its value at the unit step. -/
lemma conclusion_prony_step_conditioning_dichotomy_exponential_branch
    (x : ℝ) (hx : 1 ≤ x) :
    Real.exp (-x) ≤ Real.exp (-1) := by
  rw [Real.exp_le_exp]
  linarith

/-- The polynomial side of the dichotomy at the critical step `Δ(t)=1/t`. -/
lemma conclusion_prony_step_conditioning_dichotomy_polynomial_branch
    (κ : ℕ) (t : ℝ) (_ht : t ≠ 0) :
    (1 / (1 / t)) ^ (κ - 1) = t ^ (κ - 1) := by
  have hstep : 1 / (1 / t) = t := by
    simp
  rw [hstep]

/-- The Stieltjes-Prony lower-bound specialization at the critical step `Δ(t)=1/t`. -/
lemma conclusion_prony_step_conditioning_dichotomy_step_lower_bound
    (sep : ℝ → ℝ → ℝ) (t g0 alphaBar : ℝ) (ht : 0 < t) (hg0 : 0 < g0)
    (hstep : 1 / t ≤ Real.pi / g0)
    (hLower : ∀ {Delta : ℝ}, 0 < Delta → Delta ≤ Real.pi / g0 →
      sep t Delta ≥ Real.exp (-(t + alphaBar) * Delta) * (2 / Real.pi) * g0 * Delta) :
    sep t (1 / t) ≥ (2 / (Real.pi * Real.exp 1)) * g0 * Real.exp (-alphaBar / t) / t := by
  exact (paper_conclusion_stieltjes_prony_step_optimal_law sep t g0 alphaBar ht hg0 hstep
    hLower).2

/-- Concrete statement for the two-case Prony step/conditioning dichotomy. -/
def conclusion_prony_step_conditioning_dichotomy_statement : Prop :=
  (∀ x : ℝ, 1 ≤ x → Real.exp (-x) ≤ Real.exp (-1)) ∧
    (∀ (κ : ℕ) (t : ℝ), t ≠ 0 → (1 / (1 / t)) ^ (κ - 1) = t ^ (κ - 1)) ∧
    (∀ (sep : ℝ → ℝ → ℝ) (t g0 alphaBar : ℝ), 0 < t → 0 < g0 →
      1 / t ≤ Real.pi / g0 →
      (∀ {Delta : ℝ}, 0 < Delta → Delta ≤ Real.pi / g0 →
        sep t Delta ≥ Real.exp (-(t + alphaBar) * Delta) * (2 / Real.pi) * g0 * Delta) →
      sep t (1 / t) ≥ (2 / (Real.pi * Real.exp 1)) * g0 * Real.exp (-alphaBar / t) / t)

/-- Paper label: `thm:conclusion-prony-step-conditioning-dichotomy`. -/
theorem paper_conclusion_prony_step_conditioning_dichotomy :
    conclusion_prony_step_conditioning_dichotomy_statement := by
  refine ⟨?_, ?_, ?_⟩
  · exact conclusion_prony_step_conditioning_dichotomy_exponential_branch
  · exact conclusion_prony_step_conditioning_dichotomy_polynomial_branch
  · intro sep t g0 alphaBar ht hg0 hstep hLower
    exact conclusion_prony_step_conditioning_dichotomy_step_lower_bound sep t g0 alphaBar ht
      hg0 hstep hLower

end Omega.Conclusion
