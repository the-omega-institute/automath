import Mathlib.Tactic
import Omega.Conclusion.Window6MinimalShellRigidSubcoverRootSlice
import Omega.GU.Window6AdjointWeightMultiset

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-minimal-shell-five-three-cleavage`. -/
theorem paper_conclusion_window6_minimal_shell_five_three_cleavage :
    Omega.Conclusion.window6MinimalShell =
        Omega.Conclusion.window6CyclicFiber ∪ Omega.Conclusion.window6BoundaryFiber ∧
      Disjoint Omega.Conclusion.window6CyclicFiber Omega.Conclusion.window6BoundaryFiber ∧
      Omega.Conclusion.window6CyclicFiber.card = 5 ∧
      Omega.Conclusion.window6BoundaryFiber.card = 3 ∧
      Fintype.card Omega.Conclusion.Window6B3RootSlice = 5 ∧
      Omega.GU.boundaryZeroWeights.card = 3 := by
  rcases window6_minimal_shell_decomposition with ⟨hdisj, hcover⟩
  refine ⟨?_, hdisj.symm, by decide, by decide, by decide, by decide⟩
  simpa [Finset.union_comm] using hcover.symm

end Omega.Conclusion
