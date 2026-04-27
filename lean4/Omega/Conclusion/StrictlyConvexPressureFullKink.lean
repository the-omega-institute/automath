import Mathlib.Tactic
import Omega.Conclusion.DiscreteKinkMassHatKernelCurvature

namespace Omega.Conclusion

open MeasureTheory

noncomputable section

/-- The finite pressure model used for the full-kink certificate. -/
def conclusion_strictly_convex_pressure_full_kink_pressure (q : ℤ) : ℝ :=
  (q : ℝ) ^ 2

/-- Discrete second difference of the finite pressure model. -/
def conclusion_strictly_convex_pressure_full_kink_secondDifference (q : ℤ) : ℝ :=
  conclusion_strictly_convex_pressure_full_kink_pressure (q + 1) -
    2 * conclusion_strictly_convex_pressure_full_kink_pressure q +
      conclusion_strictly_convex_pressure_full_kink_pressure (q - 1)

/-- The finite-window kink predicate. -/
def conclusion_strictly_convex_pressure_full_kink_finiteWindowKink (q : ℤ) : Prop :=
  q ∈ Finset.Icc (-2 : ℤ) 2 ∧
    0 < conclusion_strictly_convex_pressure_full_kink_secondDifference q

lemma conclusion_strictly_convex_pressure_full_kink_secondDifference_eq_two (q : ℤ) :
    conclusion_strictly_convex_pressure_full_kink_secondDifference q = 2 := by
  unfold conclusion_strictly_convex_pressure_full_kink_secondDifference
    conclusion_strictly_convex_pressure_full_kink_pressure
  norm_num
  ring

/-- Paper-facing concrete full-kink package on the finite window `[-2,2]`. -/
def conclusion_strictly_convex_pressure_full_kink_statement : Prop :=
  (∀ q ∈ Finset.Icc (-2 : ℤ) 2,
    conclusion_strictly_convex_pressure_full_kink_finiteWindowKink q) ∧
    (∀ q ∈ Finset.Icc (-2 : ℤ) 2,
      conclusion_strictly_convex_pressure_full_kink_secondDifference q = 2) ∧
    discreteKinkMass (fun s : ℝ => s ^ 2) 0 =
      MeasureTheory.integral
        (μ := volume.restrict (Set.Icc (((0 : ℤ) : ℝ) - 1) (((0 : ℤ) : ℝ) + 1)))
        (fun s => (1 - |s - (0 : ℤ)|) * secondDeriv (fun t : ℝ => t ^ 2) s)

/-- Paper label: `thm:conclusion-strictly-convex-pressure-full-kink`. -/
theorem paper_conclusion_strictly_convex_pressure_full_kink :
    conclusion_strictly_convex_pressure_full_kink_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    exact ⟨hq, by
      rw [conclusion_strictly_convex_pressure_full_kink_secondDifference_eq_two]
      norm_num⟩
  · intro q _hq
    exact conclusion_strictly_convex_pressure_full_kink_secondDifference_eq_two q
  · have hτ : ContDiff ℝ 2 (fun s : ℝ => s ^ 2) := by
      fun_prop
    simpa using paper_conclusion_discrete_kink_mass_hat_kernel_curvature (τ := fun s : ℝ => s ^ 2)
      hτ 0

end

end Omega.Conclusion
