import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Paper label: `thm:xi-phase-fold-kernel-minimal-certificate-rank`. -/
theorem paper_xi_phase_fold_kernel_minimal_certificate_rank (rB : Nat) :
    (∀ m : Nat, (∃ f : Fin rB → Fin m, Function.Injective f) → rB ≤ m) ∧
      (∃ f : Fin rB → Fin rB, Function.Injective f) := by
  simpa using paper_cdim_phase_fold_kernel_minimal_certificate_rank rB

end Omega.CircleDimension
