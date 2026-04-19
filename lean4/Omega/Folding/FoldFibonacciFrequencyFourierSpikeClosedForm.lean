import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Omega.Core.Fib
import Omega.Folding.FoldSpectrumFactorization

namespace Omega.Folding

noncomputable section

/-- The resonant Fibonacci frequency used for the Fourier spike package. -/
def foldFibonacciResonantFrequency (m : ℕ) : ℕ :=
  Nat.fib (m + 1)

/-- The corresponding resonant angle `2π F_{m+1}`. -/
def foldFibonacciResonantAngle (m : ℕ) : ℝ :=
  (foldFibonacciResonantFrequency m : ℝ) * (2 * Real.pi)

/-- The alternating Fibonacci phase that closes to `F_{m+2} - 1`. -/
def foldFibonacciAlternatingPhase (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range ((m + 1) / 2), Nat.fib (m + 1 - 2 * k)

/-- Coordinate weights for the resonant Fourier spike. -/
def foldFibonacciFrequencySpikeWeight (m : ℕ) (i : Fin m) : ℝ :=
  (Nat.fib (m - i.1) : ℝ)

/-- Closed form of the Fibonacci-frequency Fourier spike: the alternating phase collapses to
`F_{m+2} - 1`, while the normalized Fourier transform and its modulus both equal `1` at the
resonant angle.
    thm:fold-fibonacci-frequency-fourier-spike-closed-form -/
def FoldFibonacciFrequencyFourierSpikeClosedForm (m : ℕ) : Prop :=
  foldFibonacciAlternatingPhase m = Nat.fib (m + 2) - 1 ∧
    normalizedResidueProfileFourier (foldFibonacciFrequencySpikeWeight m)
        (foldFibonacciResonantAngle m) = 1 ∧
    ‖normalizedResidueProfileFourier (foldFibonacciFrequencySpikeWeight m)
        (foldFibonacciResonantAngle m)‖ = 1

private theorem foldFibonacciCosFactor_eq_one (m : ℕ) (i : Fin m) :
    Real.cos
        (foldFibonacciFrequencySpikeWeight m i * foldFibonacciResonantAngle m) = 1 := by
  unfold foldFibonacciFrequencySpikeWeight foldFibonacciResonantAngle foldFibonacciResonantFrequency
  calc
    Real.cos ((Nat.fib (m - i.1) : ℝ) * ((Nat.fib (m + 1) : ℝ) * (2 * Real.pi)))
        = Real.cos (((Nat.fib (m - i.1) * Nat.fib (m + 1) : ℕ) : ℝ) * (2 * Real.pi)) := by
            rw [← mul_assoc, ← Nat.cast_mul]
    _ = 1 := Real.cos_nat_mul_two_pi _

theorem paper_fold_fibonacci_frequency_fourier_spike_closed_form
    (m : ℕ) : FoldFibonacciFrequencyFourierSpikeClosedForm m := by
  rcases paper_fold_spectrum_factorization
      (w := foldFibonacciFrequencySpikeWeight m)
      (θ := foldFibonacciResonantAngle m) with
    ⟨_, hNormalized, hNorm⟩
  have hNormalizedOne :
      normalizedResidueProfileFourier (foldFibonacciFrequencySpikeWeight m)
          (foldFibonacciResonantAngle m) = 1 := by
    rw [hNormalized]
    calc
      ∏ i : Fin m,
          residueProfileCosFactor (foldFibonacciFrequencySpikeWeight m i)
            (foldFibonacciResonantAngle m)
          = ∏ _i : Fin m, (1 : ℂ) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              simp [residueProfileCosFactor, foldFibonacciCosFactor_eq_one]
      _ = 1 := by simp
  have hNormOne :
      ‖normalizedResidueProfileFourier (foldFibonacciFrequencySpikeWeight m)
          (foldFibonacciResonantAngle m)‖ = 1 := by
    rw [hNorm]
    calc
      ∏ i : Fin m,
          |Real.cos
            (foldFibonacciFrequencySpikeWeight m i * foldFibonacciResonantAngle m)|
          = ∏ _i : Fin m, (1 : ℝ) := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              simp [foldFibonacciCosFactor_eq_one]
      _ = 1 := by simp
  exact ⟨Omega.fib_alternating_skip_sum m, hNormalizedOne, hNormOne⟩

end
end Omega.Folding
