import Mathlib.Algebra.BigOperators.Ring.Finset
import Omega.Folding.FoldSigmaPhiDiverges

open scoped BigOperators

namespace Omega.Folding

/-- Concrete sampling package for the Bernoulli Fourier non-`ℓ²` statement. The sampled Fourier
magnitudes are modeled by `sample`, the resonance profile is `Cphi`, and `sample_sq` records the
pointwise square identity `|μ̂(πu)|² = Cφ(u)²` used to rewrite the square sum. -/
structure FoldBernoulliFourierSamplingNotL2Data where
  Cphi : ℕ → ℝ
  sample : ℕ → ℝ
  c : ℝ
  n0 : ℕ
  hc : 0 < c
  hFib : ∀ n ≥ n0, c ≤ Cphi (Nat.fib n)
  sample_sq : ∀ u : ℕ, (sample u) ^ 2 = (Cphi u) ^ 2

namespace FoldBernoulliFourierSamplingNotL2Data

/-- The arithmetic-lattice Fourier samples are not square summable: their symmetric partial square
sums are unbounded. -/
def sampleNotSquareSummable (D : FoldBernoulliFourierSamplingNotL2Data) : Prop :=
  ∀ B : ℝ, ∃ N : ℕ,
    B ≤ 1 + 2 * Finset.sum (Finset.range (N + 1)) (fun u => (D.sample u) ^ 2)

end FoldBernoulliFourierSamplingNotL2Data

open FoldBernoulliFourierSamplingNotL2Data

/-- Paper label: `cor:fold-bernoulli-fourier-sampling-not-l2`. -/
theorem paper_fold_bernoulli_fourier_sampling_not_l2
    (D : FoldBernoulliFourierSamplingNotL2Data) : D.sampleNotSquareSummable := by
  intro B
  obtain ⟨N, hN⟩ := paper_fold_sigma_phi_diverges D.Cphi D.c D.n0 D.hc D.hFib B
  refine ⟨N, ?_⟩
  have hsum :
      Finset.sum (Finset.range (N + 1)) (fun u => (D.sample u) ^ 2) =
        Finset.sum (Finset.range (N + 1)) (fun u => (D.Cphi u) ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    exact D.sample_sq u
  calc
    B ≤ 1 + 2 * Finset.sum (Finset.range (N + 1)) (fun u => (D.Cphi u) ^ 2) := hN
    _ = 1 + 2 * Finset.sum (Finset.range (N + 1)) (fun u => (D.sample u) ^ 2) := by
      rw [hsum]

end Omega.Folding
