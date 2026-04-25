import Omega.Zeta.Conclusion74DoubleLargeSieveInput

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Paper label: `prop:gm-double-large-sieve-input`. -/
theorem paper_gm_double_large_sieve_input (N : ℕ) (hN : 2 ≤ N)
    (δ₁ δ₂ C₁ C₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (multiplicativeSum additiveSum : ℂ)
    (hmulGap : ‖multiplicativeSum‖ ≤ C₁ * (N : ℝ) * (N : ℝ) ^ (-δ₁))
    (haddGap : ‖additiveSum‖ ≤ C₂ * (N : ℝ) * (N : ℝ) ^ (-δ₂)) :
    Omega.Zeta.multiplicativeLargeSieveSaving N δ₁ C₁ multiplicativeSum ∧
      Omega.Zeta.additiveLargeSieveSaving N δ₂ C₂ additiveSum := by
  exact
    Omega.Zeta.paper_conclusion74_double_large_sieve_input N hN δ₁ δ₂ C₁ C₂ hδ₁ hδ₂
      multiplicativeSum additiveSum hmulGap haddGap

end

end Omega.SyncKernelRealInput
