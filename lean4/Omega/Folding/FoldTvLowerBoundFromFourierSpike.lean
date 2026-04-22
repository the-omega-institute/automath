import Mathlib.Tactic
import Omega.Folding.FoldFibonacciFrequencyFourierSpikeClosedForm

namespace Omega.Folding

noncomputable section

/-- The Fourier-character lower bound produced by the resonant Fibonacci spike. -/
def foldTvLowerBoundFromFourierSpike (m : ℕ) : ℝ :=
  ‖normalizedResidueProfileFourier (foldFibonacciFrequencySpikeWeight m)
      (foldFibonacciResonantAngle m)‖ / 2

/-- Paper label: `cor:fold-tv-lower-bound-from-fourier-spike`.
At the resonant Fibonacci frequency, the unit-modulus Fourier spike yields the sharp lower-bound
value `1 / 2` for the chapter-local total-variation proxy. -/
theorem paper_fold_tv_lower_bound_from_fourier_spike (m : ℕ) :
    foldTvLowerBoundFromFourierSpike m = (1 / 2 : ℝ) ∧
      0 < foldTvLowerBoundFromFourierSpike m := by
  rcases paper_fold_fibonacci_frequency_fourier_spike_closed_form m with ⟨_, _, hNorm⟩
  constructor
  · unfold foldTvLowerBoundFromFourierSpike
    rw [hNorm]
  · have hEq : foldTvLowerBoundFromFourierSpike m = (1 / 2 : ℝ) := by
      unfold foldTvLowerBoundFromFourierSpike
      rw [hNorm]
    rw [hEq]
    norm_num

end

end Omega.Folding
