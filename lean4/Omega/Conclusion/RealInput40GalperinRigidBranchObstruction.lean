import Omega.Conclusion.RealInput40RigidSqrtBranchCollisionBlindness

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-realinput40-galperin-rigid-branch-obstruction`. -/
theorem paper_conclusion_realinput40_galperin_rigid_branch_obstruction
    (D : conclusion_realinput40_rigid_sqrt_branch_collision_blindness_data) :
    (¬ ∃ u v branch, D.rigidBranchValue u branch ≠ D.rigidBranchValue v branch) ∧
      (¬ ∃ u v branch, D.zetaAuditValue u branch ≠ D.zetaAuditValue v branch) ∧
        (¬ ∃ u v branch, D.traceAuditValue u branch ≠ D.traceAuditValue v branch) := by
  rcases paper_conclusion_realinput40_rigid_sqrt_branch_collision_blindness D with
    ⟨hrigid, hzeta, htrace⟩
  constructor
  · rintro ⟨u, v, branch, hne⟩
    exact hne (hrigid u v branch)
  · constructor
    · rintro ⟨u, v, branch, hne⟩
      exact hne (hzeta u v branch)
    · rintro ⟨u, v, branch, hne⟩
      exact hne (htrace u v branch)

end Omega.Conclusion
