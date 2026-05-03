import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-window6-permutation-module-visible-hidden-splitting`. -/
theorem paper_conclusion_window6_permutation_module_visible_hidden_splitting
    (fiberPartition standardSplitting localStdTypes histogram visibleHiddenDims : Prop)
    (hpart : fiberPartition) (hsplit : fiberPartition -> standardSplitting)
    (hlocal : standardSplitting -> localStdTypes) (hhist : localStdTypes -> histogram)
    (hdims : histogram -> visibleHiddenDims) :
    standardSplitting ∧ localStdTypes ∧ histogram ∧ visibleHiddenDims := by
  have hsplit' : standardSplitting := hsplit hpart
  have hlocal' : localStdTypes := hlocal hsplit'
  have hhist' : histogram := hhist hlocal'
  exact ⟨hsplit', hlocal', hhist', hdims hhist'⟩

end Omega.Conclusion
