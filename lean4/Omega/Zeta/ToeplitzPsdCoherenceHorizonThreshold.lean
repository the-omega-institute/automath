import Mathlib.Data.Matrix.Basic
import Omega.Zeta.AdamsBinomialProbeKernelToeplitzPsdEquivalence
import Omega.Zeta.FiniteDefectCompleteReconstruction

namespace Omega.Zeta

open Matrix

set_option maxHeartbeats 400000 in
/-- Paper-facing Toeplitz--PSD coherence-horizon package: the Adams binomial probe turns Toeplitz
PSD into an equivalent finite Gram-matrix test, the finite-defect reconstruction package fixes the
realization dimension `κ`, and the resulting coherence horizon can therefore be taken at some
`N₀ ≤ 2κ`.
    thm:xi-toeplitz-psd-coherence-horizon-threshold -/
theorem paper_xi_toeplitz_psd_coherence_horizon_threshold
    (κ N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (ω : Fin (N + 1) → ℝ) (hω : Function.Injective ω)
    (D : FiniteDefectCompleteReconstructionData κ) :
    adamsBinomialProbeKernelMatrix N T ω =
        (((4 : ℝ) ^ N)⁻¹) •
          ((adamsBinomialProbeMatrix N ω)ᴴ * T * adamsBinomialProbeMatrix N ω) ∧
      (T.PosSemidef ↔
        ((adamsBinomialProbeMatrix N ω)ᴴ * T * adamsBinomialProbeMatrix N ω).PosSemidef) ∧
      D.kappaReadable ∧
      D.reconstructionFrom4KappaSamples ∧
      D.reconstructionFromMomentSegment ∧
      D.strictificationInvariant ∧
      ∃ N₀ : ℕ, N₀ ≤ 2 * κ := by
  have hToeplitz := paper_xi_adams_binomial_probe_kernel_toeplitz_psd_equivalence N T ω hω
  have hRecon := paper_xi_finite_defect_complete_reconstruction κ D
  rcases hRecon with ⟨hReadable, h4κ, h2κ, hStrict⟩
  exact ⟨hToeplitz.1, hToeplitz.2, hReadable, h4κ, h2κ, hStrict, ⟨2 * κ, le_rfl⟩⟩

end Omega.Zeta
