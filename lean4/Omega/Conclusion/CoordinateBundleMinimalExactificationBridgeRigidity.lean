import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-coordinatebundle-minimal-exactification-bridge-rigidity`.  Once deleting a tree
edge splits the compressed graph into two connected components, the screen-kernel
connected-component formula gives rank `2 - 1 = 1`. -/
theorem paper_conclusion_coordinatebundle_minimal_exactification_bridge_rigidity
    (rankKernel components : Nat) (hSplit : components = 2)
    (hRank : rankKernel = components - 1) : rankKernel = 1 := by
  subst components
  simpa using hRank

end Omega.Conclusion
