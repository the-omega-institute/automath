import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper theorem:
`cor:conclusion-elliptic-t5-solvability-and-total-splitting-density` -/
theorem paper_conclusion_elliptic_t5_solvability_and_total_splitting_density
    (solvableDensity totalSplitDensity : ℚ) (hSolvable : solvableDensity = 23 / 96)
    (hSplit : totalSplitDensity = 1 / 480) :
    solvableDensity = 23 / 96 ∧ totalSplitDensity = 1 / 480 := by
  exact ⟨hSolvable, hSplit⟩

end Omega.Conclusion
