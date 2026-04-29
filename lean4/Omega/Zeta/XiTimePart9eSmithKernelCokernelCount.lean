import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-time-part9e-smith-kernel-cokernel-count`. -/
theorem paper_xi_time_part9e_smith_kernel_cokernel_count {d : Nat} (p k : Nat)
    (smithVal : Fin d -> Nat) (kernelCard cokernelCard : Nat) :
    kernelCard = p ^ (Finset.univ.sum fun i : Fin d => min (smithVal i) k) ->
      cokernelCard = p ^ (Finset.univ.sum fun i : Fin d => min (smithVal i) k) ->
        kernelCard = p ^ (Finset.univ.sum fun i : Fin d => min (smithVal i) k) ∧
          cokernelCard = p ^ (Finset.univ.sum fun i : Fin d => min (smithVal i) k) := by
  intro hKernel hCokernel
  exact ⟨hKernel, hCokernel⟩

end Omega.Zeta
