import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Omega.Conclusion

open MeasureTheory

noncomputable section

/-- The second derivative, written via iterated `deriv`. -/
def secondDeriv (τ : ℝ → ℝ) (s : ℝ) : ℝ :=
  deriv (deriv τ) s

/-- The discrete kink mass represented by the hat-kernel average of the second derivative. -/
def discreteKinkMass (τ : ℝ → ℝ) (q : ℤ) : ℝ :=
  MeasureTheory.integral (μ := volume.restrict (Set.Icc ((q : ℝ) - 1) ((q : ℝ) + 1))) fun s =>
    (1 - |s - q|) * secondDeriv τ s

/-- Paper label: `thm:conclusion-discrete-kink-mass-hat-kernel-curvature`. -/
theorem paper_conclusion_discrete_kink_mass_hat_kernel_curvature {τ : ℝ → ℝ}
    (hτ : ContDiff ℝ 2 τ) (q : ℤ) :
    discreteKinkMass τ q =
      MeasureTheory.integral
        (μ := volume.restrict (Set.Icc ((q : ℝ) - 1) ((q : ℝ) + 1)))
        (fun s => (1 - |s - q|) * secondDeriv τ s) := by
  simpa [discreteKinkMass]

end

end Omega.Conclusion
