import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete data for the bulk/boundary speed-matching equation. -/
structure XiBulkBoundarySpeedMatchingData where
  κ : ℕ
  δ : Fin κ → ℝ
  sStar : ℝ

namespace XiBulkBoundarySpeedMatchingData

/-- The finite bulk-side reciprocal sum appearing in the matching equation. -/
noncomputable def xi_bulk_boundary_speed_matching_bulkSum
    (D : XiBulkBoundarySpeedMatchingData) (s : ℝ) : ℝ :=
  ∑ j : Fin D.κ, (1 + Real.exp s * D.δ j)⁻¹

/-- The constant on the right-hand side of the paper's explicit equation. -/
noncomputable def xi_bulk_boundary_speed_matching_matchingConstant
    (D : XiBulkBoundarySpeedMatchingData) : ℝ :=
  (D.κ : ℝ) * ((D.κ : ℝ) - 1) / (2 * (D.κ : ℝ) - 1)

/-- A concrete bulk speed whose equality with the constant boundary speed `κ` is equivalent to the
finite-sum matching equation. -/
noncomputable def xi_bulk_boundary_speed_matching_bulkSpeed
    (D : XiBulkBoundarySpeedMatchingData) (s : ℝ) : ℝ :=
  (D.κ : ℝ) + xi_bulk_boundary_speed_matching_matchingConstant D -
    xi_bulk_boundary_speed_matching_bulkSum D s

/-- Paper label: `prop:xi-bulk-boundary-speed-matching`. -/
def speedMatching (D : XiBulkBoundarySpeedMatchingData) : Prop :=
  xi_bulk_boundary_speed_matching_bulkSpeed D D.sStar = (D.κ : ℝ) ↔
    xi_bulk_boundary_speed_matching_bulkSum D D.sStar =
      xi_bulk_boundary_speed_matching_matchingConstant D

end XiBulkBoundarySpeedMatchingData

open XiBulkBoundarySpeedMatchingData

theorem paper_xi_bulk_boundary_speed_matching
    (D : XiBulkBoundarySpeedMatchingData) : D.speedMatching := by
  unfold XiBulkBoundarySpeedMatchingData.speedMatching
  unfold xi_bulk_boundary_speed_matching_bulkSpeed
  constructor <;> intro h <;> linarith

end

end Omega.Zeta
