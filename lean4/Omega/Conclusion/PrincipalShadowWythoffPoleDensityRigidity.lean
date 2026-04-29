import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-principal-shadow-wythoff-pole-density-rigidity`. -/
theorem paper_conclusion_principal_shadow_wythoff_pole_density_rigidity
    (wythoffPoleFormula beattyPartition principalMonotone noThirdBranch : Prop)
    (hw : wythoffPoleFormula) (hb : beattyPartition) (hm : principalMonotone)
    (hn : beattyPartition → noThirdBranch) :
    wythoffPoleFormula ∧ beattyPartition ∧ principalMonotone ∧ noThirdBranch := by
  exact ⟨hw, hb, hm, hn hb⟩

end Omega.Conclusion
