import Omega.Conclusion.Window6LongRootGeneratedAlgebraDoubleblock

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-long-root-commutant-closed`. -/
theorem paper_conclusion_window6_long_root_commutant_closed
    (longRootNormalForm chiralDoubleBlock orbitDoubletFactor commutantClosed : Prop)
    (hblock : longRootNormalForm -> chiralDoubleBlock)
    (horbit : chiralDoubleBlock -> orbitDoubletFactor)
    (hcomm : chiralDoubleBlock ∧ orbitDoubletFactor -> commutantClosed) :
    longRootNormalForm -> commutantClosed := by
  intro hlong
  exact hcomm
    (paper_conclusion_window6_long_root_generated_algebra_doubleblock
      longRootNormalForm chiralDoubleBlock orbitDoubletFactor hblock horbit hlong)

end Omega.Conclusion
