import Omega.SPG.NoiseBudget

namespace Omega.SPG

/-- Paper-facing dyadic holographic reconstruction noise budget threshold.
    cor:spg-dyadic-holographic-reconstruction-noise-budget -/
theorem paper_spg_dyadic_holographic_reconstruction_noise_budget
    {n m : ℕ} {ε δ : ℝ} (hn : 0 < n) :
    (((1 / Real.sqrt (2 * n : ℝ)) * (2 : ℝ) ^ (m / 2 : ℝ)) * ε ≤ δ) ↔
      ε ≤ Real.sqrt (2 * n : ℝ) * δ * (2 : ℝ) ^ (-(m / 2 : ℝ)) := by
  simpa using paper_noiseBudget_threshold_iff (n := n) (m := m) (ε := ε) (δ := δ) hn

end Omega.SPG
