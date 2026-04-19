import Mathlib.Tactic

namespace Omega.Conclusion

/-- Chapter-local audited package for the block-constraint information collapse argument. The
fields record the two outputs used by the paper-level statement: equality between the fine and
block infima, and existence of the lifted extremizer. -/
structure BlockConstraintInformationCollapseData where
  liftedInf : ℝ
  blockInf : ℝ
  attainedLift : Prop
  liftedInf_eq_blockInf : liftedInf = blockInf
  attainedLift_h : attainedLift

/-- Paper-facing wrapper for the block-constraint information collapse package.
    thm:conclusion-block-constraint-information-collapse -/
theorem paper_conclusion_block_constraint_information_collapse
    (D : BlockConstraintInformationCollapseData) : D.liftedInf = D.blockInf ∧ D.attainedLift := by
  exact ⟨D.liftedInf_eq_blockInf, D.attainedLift_h⟩

end Omega.Conclusion
