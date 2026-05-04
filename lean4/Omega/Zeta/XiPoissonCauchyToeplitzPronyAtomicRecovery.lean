import Omega.CircleDimension.AtomicDefectProny2KappaRecovery

namespace Omega.Zeta

/-- Paper label: `prop:xi-poisson-cauchy-toeplitz-prony-atomic-recovery`. -/
theorem paper_xi_poisson_cauchy_toeplitz_prony_atomic_recovery
    (N : ℕ) (deltaStep : ℝ) (depths : Fin N → ℝ) (amplitudes : Fin N → ℂ)
    (hdeltaStep : 0 < deltaStep) (hdepths : Function.Injective depths) :
    let V : Matrix (Fin N) (Fin N) ℂ :=
      Omega.CircleDimension.atomicDefectVandermonde deltaStep depths
    let samples : Fin (2 * N) → ℂ :=
      Omega.CircleDimension.atomicDefectSampleWindow deltaStep depths amplitudes
    V.det ≠ 0 ∧
      (∀ n : Fin (2 * N),
        samples n =
          Omega.CircleDimension.atomicDefectSample deltaStep depths amplitudes n) ∧
      (∀ altAmplitudes : Fin N → ℂ,
        (∀ n : Fin N,
          Omega.CircleDimension.atomicDefectSample deltaStep depths altAmplitudes n =
            Omega.CircleDimension.atomicDefectSample deltaStep depths amplitudes n) →
        altAmplitudes = amplitudes) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · exact Omega.CircleDimension.atomicDefectVandermonde_det_ne_zero hdeltaStep hdepths
  · intro n
    rfl
  · intro altAmplitudes hsamples
    exact Omega.CircleDimension.atomicDefectAmplitudes_unique hdeltaStep hdepths amplitudes
      altAmplitudes hsamples

end Omega.Zeta
