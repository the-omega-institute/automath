import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.Window6AuditBoundaryCertificates

namespace Omega.Zeta

open Omega.TypedAddressBiaxialCompletion

/-- Paper label: `prop:xi-time-part60ab3-window6-boundary-center-residual`. The audited
window-`6` boundary certificate gives a rank-three center, one geometric diagonal bit, and a
rank-two residual quotient. -/
theorem paper_xi_time_part60ab3_window6_boundary_center_residual :
    window6BoundaryCenterRank = 3 ∧
      (2 : Nat) ^ window6BoundaryCenterRank = 8 ∧
      window6BoundaryGeometricRank = 1 ∧
      window6BoundaryQuotientRank = 2 := by
  rcases paper_typed_address_biaxial_completion_window6_audit_boundary_certificates with
    ⟨hCenterRank, hCenterCard, hGeometricRank, _, hQuotientRank, _, _, _⟩
  exact ⟨hCenterRank, hCenterCard, hGeometricRank, hQuotientRank⟩

end Omega.Zeta
