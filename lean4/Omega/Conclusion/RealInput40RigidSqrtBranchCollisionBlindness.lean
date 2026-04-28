import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete branch and audit data for the real-input-40 rigid square-root package. -/
structure conclusion_realinput40_rigid_sqrt_branch_collision_blindness_data where
  conclusion_realinput40_rigid_sqrt_branch_collision_blindness_branchValue : Bool → ℝ
  conclusion_realinput40_rigid_sqrt_branch_collision_blindness_zetaAudit : Bool → ℝ
  conclusion_realinput40_rigid_sqrt_branch_collision_blindness_traceAudit : Bool → ℝ

/-- Rigid branch values, factored through the square-root branch and hence independent of `u`. -/
def conclusion_realinput40_rigid_sqrt_branch_collision_blindness_data.rigidBranchValue
    (D : conclusion_realinput40_rigid_sqrt_branch_collision_blindness_data)
    (_u : ℝ) (branch : Bool) : ℝ :=
  D.conclusion_realinput40_rigid_sqrt_branch_collision_blindness_branchValue branch

/-- The zeta audit attached to a rigid branch; it is independent of the collision parameter. -/
def conclusion_realinput40_rigid_sqrt_branch_collision_blindness_data.zetaAuditValue
    (D : conclusion_realinput40_rigid_sqrt_branch_collision_blindness_data)
    (_u : ℝ) (branch : Bool) : ℝ :=
  D.conclusion_realinput40_rigid_sqrt_branch_collision_blindness_zetaAudit branch

/-- The trace audit attached to a rigid branch; it is independent of the collision parameter. -/
def conclusion_realinput40_rigid_sqrt_branch_collision_blindness_data.traceAuditValue
    (D : conclusion_realinput40_rigid_sqrt_branch_collision_blindness_data)
    (_u : ℝ) (branch : Bool) : ℝ :=
  D.conclusion_realinput40_rigid_sqrt_branch_collision_blindness_traceAudit branch

/-- Rigid square-root branches are blind to changes in the collision parameter. -/
def conclusion_realinput40_rigid_sqrt_branch_collision_blindness_data.rigidBranchesBlind
    (D : conclusion_realinput40_rigid_sqrt_branch_collision_blindness_data) : Prop :=
  ∀ u v branch, D.rigidBranchValue u branch = D.rigidBranchValue v branch

/-- The zeta and trace audit channels inherit the same collision-parameter blindness. -/
def conclusion_realinput40_rigid_sqrt_branch_collision_blindness_data.zetaTraceAuditsBlind
    (D : conclusion_realinput40_rigid_sqrt_branch_collision_blindness_data) : Prop :=
  (∀ u v branch, D.zetaAuditValue u branch = D.zetaAuditValue v branch) ∧
    ∀ u v branch, D.traceAuditValue u branch = D.traceAuditValue v branch

/-- Paper label: `thm:conclusion-realinput40-rigid-sqrt-branch-collision-blindness`. -/
theorem paper_conclusion_realinput40_rigid_sqrt_branch_collision_blindness
    (D : conclusion_realinput40_rigid_sqrt_branch_collision_blindness_data) :
    D.rigidBranchesBlind ∧ D.zetaTraceAuditsBlind := by
  constructor
  · intro u v branch
    rfl
  · constructor
    · intro u v branch
      rfl
    · intro u v branch
      rfl

end Omega.Conclusion
