import Mathlib
import Omega.Zeta.ContractiveBoundaryZero

namespace Omega.Zeta

/-- Paper label: `thm:xi-contract-defect-critical-slice-principle`.
The contractive self-dual seed gives boundary nonvanishing for the completed determinant. Hence any
certified zero is forced onto the unitary slice, and the supplied completion-map criterion
`‖u(s)‖ = 1 ↔ Re(s) = 1/2` transports that slice statement to the critical line. -/
theorem paper_xi_contract_defect_critical_slice_principle
    (D : ContractiveSelfdualFamilyData) (u : ℂ → ℂ) (s0 : ℂ)
    (hu : ∀ s : ℂ, ‖u s‖ = 1 ↔ s.re = (1 : ℝ) / 2)
    (hzero : xiContractiveDeterminant D (u s0) = 0) :
    XiContractiveBoundaryZero D ∧ ‖u s0‖ = 1 ∧ s0.re = (1 : ℝ) / 2 := by
  have hboundary : XiContractiveBoundaryZero D := paper_xi_contractive_boundary_zero D
  have hcritical : s0.re = (1 : ℝ) / 2 :=
    paper_xi_contractive_critical_slice_rigidity D u s0 hu hzero
  have hunitary : ‖u s0‖ = 1 := (hu s0).2 hcritical
  exact ⟨hboundary, hunitary, hcritical⟩

end Omega.Zeta
