import Omega.Conclusion.CoordinateBundleArbitraryCompletionSharpLowerBound
import Omega.Conclusion.CoordinateBundleOneCoordinateWorthMBits

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-integrable-screen-codimension-exponential-purestar`. -/
theorem paper_conclusion_integrable_screen_codimension_exponential_purestar (m n s t : ℕ) :
    coordinateBundleAuditGap m n s = 2 ^ (m * (n - s)) ∧
      (s < n →
        coordinateBundleAuditGap m n s = 2 ^ m * coordinateBundleAuditGap m n (s + 1)) ∧
      conclusion_coordinatebundle_arbitrary_completion_sharp_lower_bound_residual_gap m n s t =
        max (coordinateBundleAuditGap m n s - t) 0 ∧
      (∀ e : ℕ,
        coordinateBundleMinimalExactification m n s e ↔
          coordinateBundleSpanningTreeEdgeCount m n s e) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact paper_conclusion_coordinatebundle_codimension_exponential_defect m n s
  · intro hs
    exact paper_conclusion_coordinatebundle_one_coordinate_worth_m_bits m n s hs
  · exact (paper_conclusion_coordinatebundle_arbitrary_completion_sharp_lower_bound m n s t).1
  · exact (paper_conclusion_coordinatebundle_all_minimal_exactifications_spanning_trees m n s).2.1

end Omega.Conclusion
