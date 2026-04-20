import Mathlib.Tactic

namespace Omega.GU

/-- Audited common fiber size on the boundary uplift at windows `6`, `7`, `8`. -/
def auditedBoundaryFiberSize (m : ℕ) : ℕ :=
  match m with
  | 6 => 2
  | 7 => 3
  | 8 => 3
  | _ => 0

/-- Audited number of boundary fibers in the uplift table. -/
def auditedBoundaryFiberCount (m : ℕ) : ℕ :=
  match m with
  | 6 => 3
  | 7 => 1
  | 8 => 1
  | _ => 0

/-- Center rank of the symmetric-group boundary factor contributed by a single audited fiber. -/
def auditedBoundaryFiberCenterRank (d : ℕ) : ℕ :=
  if d = 2 then 1 else 0

/-- Total rank of the boundary central charge in the audited dyadic uplift table. -/
def auditedBoundaryCenterRank (m : ℕ) : ℕ :=
  auditedBoundaryFiberCount m * auditedBoundaryFiberCenterRank (auditedBoundaryFiberSize m)

/-- The audited boundary central charge is nontrivial only at window `6`.
    thm:window6-boundary-central-charge-unique-among-audited-lifts -/
theorem paper_window6_boundary_central_charge_unique_among_audited_lifts :
    auditedBoundaryCenterRank 6 = 3 ∧
      auditedBoundaryCenterRank 7 = 0 ∧ auditedBoundaryCenterRank 8 = 0 := by
  native_decide

end Omega.GU
