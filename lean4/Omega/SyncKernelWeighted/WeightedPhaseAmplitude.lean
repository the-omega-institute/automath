import Omega.SyncKernelWeighted.UnitarySliceHalfPhaseLocking
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The completed discriminant root in the invariant `s = 2 cos (θ / 2)` coordinate. -/
def weightedPhaseAmplitudeCompletedRoot (s : ℝ) : ℝ := s + 3

/-- The corresponding amplitude factor `Λ(s) = 1 / w_*(s)`. -/
def weightedPhaseAmplitudeAmplitude (s : ℝ) : ℝ := 1 / weightedPhaseAmplitudeCompletedRoot s

/-- The minimal pole after transporting the completed root back to the `u = r²` coordinate. -/
def weightedPhaseAmplitudePole (θ : ℝ) : ℂ :=
  (weightedPhaseAmplitudeCompletedRoot (2 * Real.cos (θ / 2)) : ℂ) / unitarySliceHalfPhase θ

/-- The Perron branch in phase-amplitude form. -/
def weightedPhaseAmplitudeLambda (θ : ℝ) : ℂ :=
  unitarySliceHalfPhase θ *
    (weightedPhaseAmplitudeAmplitude (2 * Real.cos (θ / 2)) : ℂ)

/-- Paper label: `cor:sync-kernel-weighted-phase-amplitude`.
For the concrete completed root `w_*(s) = s + 3`, the unit-circle substitution
`u = r²`, `r = exp(i θ / 2)`, `s = 2 cos (θ / 2)` preserves the pole modulus because
`|r| = 1`, and the Perron branch splits as the half-phase times the real amplitude. -/
theorem paper_sync_kernel_weighted_phase_amplitude :
    ∀ θ : ℝ,
      let r := unitarySliceHalfPhase θ
      let s := 2 * Real.cos (θ / 2)
      ‖r‖ = 1 ∧
        weightedPhaseAmplitudePole θ =
          (weightedPhaseAmplitudeCompletedRoot s : ℂ) / r ∧
        weightedPhaseAmplitudeLambda θ =
          r * (weightedPhaseAmplitudeAmplitude s : ℂ) := by
  intro θ
  dsimp
  refine ⟨?_, rfl, rfl⟩
  simpa [unitarySliceHalfPhase] using Complex.norm_exp_ofReal_mul_I (θ / 2)

end

end Omega.SyncKernelWeighted
