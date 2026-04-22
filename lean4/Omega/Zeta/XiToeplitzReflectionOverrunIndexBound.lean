import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.ToeplitzPsdCoherenceHorizonThreshold
import Omega.Zeta.XiHorizonReflectionFiniteWitness

namespace Omega.Zeta

open Matrix

/-- Concrete data for the overrun-index bound: a finite-defect Toeplitz package together with a
candidate minimal bad Schur level. The fields are arithmetic and analytic data, not abstract paper
claims. -/
structure xi_toeplitz_reflection_overrun_index_bound_data where
  κ : ℕ
  N : ℕ
  T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  ω : Fin (N + 1) → ℝ
  hω : Function.Injective ω
  reconstruction :
    FiniteDefectCompleteReconstructionData κ
  alpha : Nat → Complex
  minimalBadLevel : ℕ
  prefixSchur :
    ∀ n, n < minimalBadLevel → Complex.abs (alpha n) < 1
  badAtMinimal :
    1 ≤ Complex.abs (alpha minimalBadLevel)

/-- The horizon theorem supplies a finite Toeplitz cutoff, while the minimal bad Schur level keeps
the pre-overrun coefficients inside the unit disk and forces the overrun coefficient to cross the
unit circle. -/
def xi_toeplitz_reflection_overrun_index_bound_statement
    (D : xi_toeplitz_reflection_overrun_index_bound_data) : Prop :=
  adamsBinomialProbeKernelMatrix D.N D.T D.ω =
      (((4 : ℝ) ^ D.N)⁻¹) •
        ((adamsBinomialProbeMatrix D.N D.ω)ᴴ * D.T * adamsBinomialProbeMatrix D.N D.ω) ∧
    (D.T.PosSemidef ↔
      ((adamsBinomialProbeMatrix D.N D.ω)ᴴ * D.T * adamsBinomialProbeMatrix D.N D.ω).PosSemidef) ∧
    D.reconstruction.kappaReadable ∧
    D.reconstruction.reconstructionFrom4KappaSamples ∧
    D.reconstruction.reconstructionFromMomentSegment ∧
    D.reconstruction.strictificationInvariant ∧
    ∃ N₀ : ℕ, N₀ ≤ 2 * D.κ ∧
      (∀ n, n < D.minimalBadLevel → Complex.abs (D.alpha n) < 1) ∧
      1 ≤ Complex.abs (D.alpha D.minimalBadLevel) ∧
      ¬ XiSchurParameters D.alpha

/-- Paper label: `cor:xi-toeplitz-reflection-overrun-index-bound`. -/
theorem paper_xi_toeplitz_reflection_overrun_index_bound
    (D : xi_toeplitz_reflection_overrun_index_bound_data) :
    xi_toeplitz_reflection_overrun_index_bound_statement D := by
  rcases paper_xi_toeplitz_psd_coherence_horizon_threshold
      D.κ D.N D.T D.ω D.hω D.reconstruction with
    ⟨hKernel, hPSD, hReadable, h4κ, h2κ, hStrict, ⟨N₀, hN₀⟩⟩
  refine ⟨hKernel, hPSD, hReadable, h4κ, h2κ, hStrict, ⟨N₀, hN₀, D.prefixSchur,
    D.badAtMinimal, ?_⟩⟩
  intro hSchur
  rcases paper_xi_horizon_reflection_finite_witness D.alpha hSchur with ⟨_, hNoBad⟩
  exact hNoBad ⟨D.minimalBadLevel, D.badAtMinimal⟩

end Omega.Zeta
