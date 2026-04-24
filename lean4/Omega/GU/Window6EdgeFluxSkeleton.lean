import Omega.GU.Window6EdgeFluxMaxEntropyKernelUniqueness

namespace Omega.GU

open scoped BigOperators

/-- Paper label: `thm:terminal-window6-edge-flux-skeleton`. -/
theorem paper_terminal_window6_edge_flux_skeleton :
    Window6EdgeFluxRowStochastic window6EdgeFluxAuditKernel ∧
      (∑ i, window6EdgeFluxAuditStationary i = 1) ∧
      (∀ i j,
        window6EdgeFluxAuditStationary i * window6EdgeFluxAuditKernel i j =
          window6EdgeFluxAuditStationary j * window6EdgeFluxAuditKernel j i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [window6EdgeFluxAuditKernel, Fin.sum_univ_four]
  · norm_num [window6EdgeFluxAuditStationary, Fin.sum_univ_four]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [window6EdgeFluxAuditStationary, window6EdgeFluxAuditKernel]

end Omega.GU
