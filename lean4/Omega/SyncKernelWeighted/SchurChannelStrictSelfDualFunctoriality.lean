import Omega.SyncKernelWeighted.KernelSelfDualCharacterSchur

namespace Omega.SyncKernelWeighted

open Matrix

noncomputable section

/-- Paper label: `thm:sync-kernel-schur-channel-strict-self-dual-functoriality`.
The untwisted Schur channel is the specialization `χ(g₁) = 1` of the Schur-component
self-duality package. -/
theorem paper_sync_kernel_schur_channel_strict_self_dual_functoriality {n : Type*} [Fintype n]
    [DecidableEq n] (q : ℕ) (u z : ℂ) (B Buinv P : Matrix n n ℂ) (hP : IsUnit P.det)
    (hsim : schurSimilarityLaw q u 1 B Buinv P) :
    schurSimilarityLaw q u 1 B Buinv P ∧ schurDeterminantFunctionalEquation q u 1 z B Buinv := by
  simpa using
    (paper_kernel_self_dual_character_schur (n := n) (q := q) u (1 : ℂ) z B Buinv P hP hsim)

end

end Omega.SyncKernelWeighted
