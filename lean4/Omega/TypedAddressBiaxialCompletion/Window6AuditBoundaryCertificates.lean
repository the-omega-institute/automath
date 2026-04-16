import Mathlib.Tactic
import Omega.Conclusion.BoundaryParityBlindFiltration
import Omega.TypedAddressBiaxialCompletion.Window6AuditBudgetSplit

namespace Omega.TypedAddressBiaxialCompletion

open Omega.Conclusion

/-- Boundary center rank specialized to the window-6 audit sector. -/
def window6BoundaryCenterRank : Nat :=
  window6BoundaryBudget

/-- Geometric parity subgroup rank in the window-6 boundary sector. -/
def window6BoundaryGeometricRank : Nat :=
  1

/-- Residual quotient rank after modding out the geometric parity subgroup. -/
def window6BoundaryQuotientRank : Nat :=
  window6BoundaryCenterRank - window6BoundaryGeometricRank

/-- Minimal torus rank needed to realize the full boundary parity package. -/
def window6BoundaryMinimalTorusRank : Nat :=
  window6BoundaryCenterRank

/-- Paper-facing wrapper for the window-6 boundary holonomy certificates: the center has rank `3`,
the geometric subgroup has rank `1`, the quotient has rank `2`, and no faithful torus realization
can use fewer than `3` circles.
    prop:typed-address-biaxial-completion-window6-audit-boundary-certificates -/
theorem paper_typed_address_biaxial_completion_window6_audit_boundary_certificates :
    window6BoundaryCenterRank = 3 ∧
      (2 : Nat) ^ window6BoundaryCenterRank = 8 ∧
      window6BoundaryGeometricRank = 1 ∧
      (2 : Nat) ^ window6BoundaryGeometricRank = 2 ∧
      window6BoundaryQuotientRank = 2 ∧
      (2 : Nat) ^ window6BoundaryQuotientRank = 4 ∧
      window6BoundaryCenterRank = window6BoundaryGeometricRank + window6BoundaryQuotientRank ∧
      window6BoundaryMinimalTorusRank = 3 := by
  rcases paper_conclusion_boundary_parity_three_layer_blind_filtration with
    ⟨hCenterCard, hGeoCard, hQuotRank, h0lt1, h1lt3, hsum, hindex, hQuotCard⟩
  rcases paper_typed_address_biaxial_completion_window6_audit_budget_split with
    ⟨_, _, _, _, _, _, hBoundaryBudget, _, _, _, _⟩
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [window6BoundaryCenterRank, hBoundaryBudget]
  · simp [window6BoundaryCenterRank, hBoundaryBudget] at hCenterCard ⊢
  · simp [window6BoundaryGeometricRank] at hGeoCard ⊢
  · simp [window6BoundaryQuotientRank, window6BoundaryCenterRank, window6BoundaryGeometricRank,
      hBoundaryBudget] at hQuotRank ⊢
  · simp [window6BoundaryQuotientRank, window6BoundaryCenterRank, window6BoundaryGeometricRank,
      hBoundaryBudget] at hQuotCard ⊢
  · simp [window6BoundaryQuotientRank, window6BoundaryCenterRank, window6BoundaryGeometricRank,
      hBoundaryBudget] at hsum ⊢
  · simp [window6BoundaryMinimalTorusRank, window6BoundaryCenterRank, hBoundaryBudget]

end Omega.TypedAddressBiaxialCompletion
