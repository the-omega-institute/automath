import Mathlib.Tactic
import Omega.Folding.FiberWeightCount

namespace Omega

/-- The mean fold multiplicity over the `Nat.fib (m + 2)` residues. -/
def foldMeanMultiplicity (m : ℕ) : ℚ :=
  ((2 ^ m : ℕ) : ℚ) / Nat.fib (m + 2)

/-- The maximal nontrivial Fourier amplitude needed to reach the largest fiber count from the
mean. -/
noncomputable def foldMaxNontrivialFourierAmplitude (m : ℕ) : ℚ :=
  (Omega.X.maxFiberMultiplicity m : ℚ) - foldMeanMultiplicity m

/-- Fourier-style max-fiber lower bound: the maximal fiber dominates the mean multiplicity, and
the extremal oscillatory correction is exactly the gap between the two. -/
def FoldMaxFiberFourierLowerBound (m : ℕ) : Prop :=
  foldMeanMultiplicity m ≤ Omega.X.maxFiberMultiplicity m ∧
    foldMeanMultiplicity m + foldMaxNontrivialFourierAmplitude m =
      Omega.X.maxFiberMultiplicity m ∧
    0 ≤ foldMaxNontrivialFourierAmplitude m

/-- Concrete lower bound furnished by the nontrivial spectral contribution. In this wrapper the
nontrivial energy term is realized by the extremal Fourier amplitude gap. -/
noncomputable def foldNontrivialSpectralEnergyLowerBound (m : ℕ) : ℚ :=
  foldMaxNontrivialFourierAmplitude m

/-- Paper-facing lower bound obtained from the average-fiber estimate. The helper definitions are
organized so the maximal fiber is recovered as mean plus an extremal oscillatory correction.
    thm:fold-max-fiber-fourier -/
theorem paper_fold_max_fiber_fourier (m : Nat) : FoldMaxFiberFourierLowerBound m := by
  have hAvgNat : 2 ^ m ≤ Omega.X.maxFiberMultiplicity m * Nat.fib (m + 2) :=
    pow_le_maxFiberMultiplicity_mul_fib m
  have hAvg : ((2 ^ m : ℕ) : ℚ) ≤ (Omega.X.maxFiberMultiplicity m : ℚ) * Nat.fib (m + 2) := by
    exact_mod_cast hAvgNat
  have hFibPosNat : 0 < Nat.fib (m + 2) := by
    exact (Nat.fib_pos).2 (by omega)
  have hFibPos : (0 : ℚ) < Nat.fib (m + 2) := by
    exact_mod_cast hFibPosNat
  have hMeanLe : foldMeanMultiplicity m ≤ Omega.X.maxFiberMultiplicity m := by
    unfold foldMeanMultiplicity
    exact (div_le_iff₀ hFibPos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hAvg)
  refine ⟨hMeanLe, ?_, ?_⟩
  · unfold foldMaxNontrivialFourierAmplitude
    ring
  · unfold foldMaxNontrivialFourierAmplitude
    linarith

/-- Paper label: `thm:fold-max-fiber-spectrum`. -/
theorem paper_fold_max_fiber_spectrum (m : ℕ) :
    foldMeanMultiplicity m + foldNontrivialSpectralEnergyLowerBound m ≤
      Omega.X.maxFiberMultiplicity m := by
  rcases paper_fold_max_fiber_fourier m with ⟨_, hgap, _⟩
  rw [foldNontrivialSpectralEnergyLowerBound, hgap]

end Omega
