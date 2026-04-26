import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Omega.Folding.FoldCriticalResonanceConstantIntegerLadder
import Omega.Folding.FoldMaxFiberFourier

namespace Omega

/-- The distinguished ladder frequency `k_m(u)` used to read off the max-fiber bias. -/
def fold_maxfiber_bias_resonance_ladder_frequency (u m : ℕ) : ℤ :=
  Omega.Folding.foldCriticalResonanceIntegerRepresentative (u : ℤ) m

/-- The normalized amplitude `a_m(k)` obtained by evaluating the max-fiber Fourier gap at the
distinguished ladder frequency and setting all other modes to zero in this wrapper. -/
noncomputable def fold_maxfiber_bias_resonance_ladder_amplitude (u m : ℕ) (k : ℤ) : ℚ :=
  if k = fold_maxfiber_bias_resonance_ladder_frequency u m then foldMaxNontrivialFourierAmplitude m
  else 0

/-- Paper label: `cor:fold-maxfiber-bias-resonance-ladder`. The integer ladder representative
`k_m(u)` lies in the canonical Fibonacci residue interval, and evaluating the normalized
amplitude at that frequency recovers the max-fiber Fourier gap with its nonnegativity. -/
theorem paper_fold_maxfiber_bias_resonance_ladder (u : Nat) :
    ∀ m : ℕ, 1 ≤ m →
      let k := fold_maxfiber_bias_resonance_ladder_frequency u m
      0 ≤ k ∧
        k < Nat.fib (m + 2) ∧
        k ≡ (u : ℤ) * Nat.fib m [ZMOD Nat.fib (m + 2)] ∧
        foldMeanMultiplicity m ≤ Omega.X.maxFiberMultiplicity m ∧
        foldMeanMultiplicity m + fold_maxfiber_bias_resonance_ladder_amplitude u m k =
          Omega.X.maxFiberMultiplicity m ∧
        fold_maxfiber_bias_resonance_ladder_amplitude u m k = foldMaxNontrivialFourierAmplitude m ∧
        0 ≤ fold_maxfiber_bias_resonance_ladder_amplitude u m k := by
  intro m hm
  dsimp [fold_maxfiber_bias_resonance_ladder_frequency]
  rcases Omega.Folding.paper_fold_critical_resonance_constant_integer_ladder (u : ℤ) m hm with
    ⟨hk0, hkFib, hkMod⟩
  rcases paper_fold_max_fiber_fourier m with ⟨hMean, hGap, hNonneg⟩
  have hkEq :
      Folding.foldCriticalResonanceIntegerRepresentative (u : ℤ) m =
        fold_maxfiber_bias_resonance_ladder_frequency u m := rfl
  refine ⟨hk0, hkFib, hkMod, hMean, ?_, ?_, ?_⟩
  · simpa [fold_maxfiber_bias_resonance_ladder_amplitude, hkEq] using hGap
  · simp [fold_maxfiber_bias_resonance_ladder_amplitude, hkEq]
  · simpa [fold_maxfiber_bias_resonance_ladder_amplitude, hkEq] using hNonneg

end Omega
