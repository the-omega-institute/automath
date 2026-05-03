import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-long-root-generated-algebra-doubleblock`. -/
theorem paper_conclusion_window6_long_root_generated_algebra_doubleblock
    (longRootNormalForm chiralDoubleBlock orbitDoubletFactor : Prop)
    (hblock : longRootNormalForm -> chiralDoubleBlock)
    (horbit : chiralDoubleBlock -> orbitDoubletFactor) :
    longRootNormalForm -> chiralDoubleBlock ∧ orbitDoubletFactor := by
  intro hlong
  have hchiral : chiralDoubleBlock := hblock hlong
  exact ⟨hchiral, horbit hchiral⟩

end Omega.Conclusion
