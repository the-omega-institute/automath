import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The equispaced weak-coherence second-difference defect
`η(Δ) = -Δ² exp(-Δ)`. -/
noncomputable def conclusion_equispaced_weak_coherence_per_step_loop_entropy_law_eta
    (Δ : ℝ) : ℝ :=
  -Δ ^ 2 * Real.exp (-Δ)

/-- The displayed per-step loop-entropy scale. -/
noncomputable def conclusion_equispaced_weak_coherence_per_step_loop_entropy_law_scale
    (Δ : ℝ) : ℝ :=
  Δ ^ 4 * Real.exp (-2 * Δ)

/-- Concrete equispaced specialization: after substituting the common defect, the normalized
per-step loop entropy is the square of that defect and hence has scale `Δ⁴ exp(-2Δ)`. -/
def conclusion_equispaced_weak_coherence_per_step_loop_entropy_law_statement : Prop :=
  ∀ Δ η : ℝ,
    η = conclusion_equispaced_weak_coherence_per_step_loop_entropy_law_eta Δ →
      η ^ 2 = conclusion_equispaced_weak_coherence_per_step_loop_entropy_law_scale Δ

/-- Paper label: `thm:conclusion-equispaced-weak-coherence-per-step-loop-entropy-law`. -/
theorem paper_conclusion_equispaced_weak_coherence_per_step_loop_entropy_law :
    conclusion_equispaced_weak_coherence_per_step_loop_entropy_law_statement := by
  intro Δ η hη
  rw [hη]
  unfold conclusion_equispaced_weak_coherence_per_step_loop_entropy_law_eta
    conclusion_equispaced_weak_coherence_per_step_loop_entropy_law_scale
  have hexp : Real.exp (-Δ) * Real.exp (-Δ) = Real.exp (-2 * Δ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show (-Δ ^ 2 * Real.exp (-Δ)) ^ 2 =
      Δ ^ 4 * (Real.exp (-Δ) * Real.exp (-Δ)) by ring, hexp]

end Omega.Conclusion
