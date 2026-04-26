import Omega.Conclusion.DiscreteKinkMassHatKernelCurvature

namespace Omega.Conclusion

open MeasureTheory

noncomputable section

/-- The tent kernel centered at an integer fan midpoint. -/
def conclusion_discrete_fan_width_tent_kernel_tomography_tent (center t : ℝ) : ℝ :=
  1 - |t - center|

/-- Measure-valued tent-kernel sample on the fan window `[q - 2, q]`. -/
def conclusion_discrete_fan_width_tent_kernel_tomography_measureSample
    (μ : Measure ℝ) (q : ℤ) : ℝ :=
  ∫ t,
    conclusion_discrete_fan_width_tent_kernel_tomography_tent ((q : ℝ) - 1) t ∂
      μ.restrict (Set.Icc ((q : ℝ) - 2) (q : ℝ))

/-- Smooth curvature sample, expressed through the already formalized second derivative. -/
def conclusion_discrete_fan_width_tent_kernel_tomography_smoothSample
    (Λ : ℝ → ℝ) (q : ℤ) : ℝ :=
  ∫ t,
    conclusion_discrete_fan_width_tent_kernel_tomography_tent ((q : ℝ) - 1) t *
      secondDeriv Λ t ∂
      volume.restrict (Set.Icc ((q : ℝ) - 2) (q : ℝ))

/-- The discrete fan width represented by the smooth tent-kernel sample. -/
def conclusion_discrete_fan_width_tent_kernel_tomography_width (Λ : ℝ → ℝ) (q : ℤ) : ℝ :=
  conclusion_discrete_fan_width_tent_kernel_tomography_smoothSample Λ q

/-- Concrete statement for the measure and smooth tent-kernel tomography identities. -/
def conclusion_discrete_fan_width_tent_kernel_tomography_statement : Prop :=
  (∀ (μ : Measure ℝ) (q : ℤ),
    conclusion_discrete_fan_width_tent_kernel_tomography_measureSample μ q =
      ∫ t,
        conclusion_discrete_fan_width_tent_kernel_tomography_tent ((q : ℝ) - 1) t ∂
          μ.restrict (Set.Icc ((q : ℝ) - 2) (q : ℝ))) ∧
  (∀ (Λ : ℝ → ℝ) (q : ℤ),
    conclusion_discrete_fan_width_tent_kernel_tomography_smoothSample Λ q =
      discreteKinkMass Λ (q - 1)) ∧
  ∀ (Λ : ℝ → ℝ) (q : ℤ),
    conclusion_discrete_fan_width_tent_kernel_tomography_width Λ q =
      conclusion_discrete_fan_width_tent_kernel_tomography_smoothSample Λ q

/-- Paper label: `thm:conclusion-discrete-fan-width-tent-kernel-tomography`. -/
theorem paper_conclusion_discrete_fan_width_tent_kernel_tomography :
    conclusion_discrete_fan_width_tent_kernel_tomography_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ q
    rfl
  · intro Λ q
    simp only [conclusion_discrete_fan_width_tent_kernel_tomography_smoothSample,
      conclusion_discrete_fan_width_tent_kernel_tomography_tent, discreteKinkMass,
      Int.cast_sub, Int.cast_one]
    rw [show (q : ℝ) - 1 - 1 = (q : ℝ) - 2 by ring]
    rw [show (q : ℝ) - 1 + 1 = (q : ℝ) by ring]
  · intro Λ q
    rfl

end

end Omega.Conclusion
