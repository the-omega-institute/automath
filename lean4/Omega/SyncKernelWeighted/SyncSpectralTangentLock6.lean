import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.SyncKernelWeighted.RateCenterPerronDegreeMultiple6
import Omega.SyncKernelWeighted.SyncSpectralTangentLock

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Paper label: `cor:sync-spectral-tangent-lock-6`. The degree-six center-slice factorization
enumerates six nonzero spectral branches at `u = 1`, and the single-branch tangent-lock theorem
applies to each of them. -/
theorem paper_sync_spectral_tangent_lock_6 :
    rateCenterPerronQ 1 ≠ 0 ∧
      rateCenterRamificationIndex = 6 ∧
      ∀ i : Fin 6,
        (∀ θ : ℝ, sync_spectral_tangent_lock_mu θ = sync_spectral_tangent_lock_mu (-θ)) ∧
          HasDerivAt sync_spectral_tangent_lock_mu 0 0 ∧
          HasDerivAt (fun θ : ℝ => Real.log (sync_spectral_tangent_lock_lambda θ)) (1 / 2) 0 := by
  refine ⟨rateCenterPerronQ_one_ne_zero, rateCenter_ramificationIndex_eq_six, ?_⟩
  intro _
  simpa using paper_sync_spectral_tangent_lock

end

end Omega.SyncKernelWeighted
