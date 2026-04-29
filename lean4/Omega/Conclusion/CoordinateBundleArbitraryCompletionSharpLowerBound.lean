import Mathlib.Tactic
import Omega.Conclusion.CoordinateBundleAllMinimalExactificationsSpanningTrees
import Omega.Conclusion.CoordinateBundleCodimensionExponentialDefect

namespace Omega.Conclusion

/-- Residual audit gap after adding `t` extra faces to the internal screen. -/
def conclusion_coordinatebundle_arbitrary_completion_sharp_lower_bound_residual_gap
    (m n s t : ℕ) : ℕ :=
  coordinateBundleAuditGap m n s - t

/-- Exactifiability within budget `t`, encoded by the existence of a minimal exactification whose
edge count does not exceed `t`. -/
def conclusion_coordinatebundle_arbitrary_completion_sharp_lower_bound_exactifiable
    (m n s t : ℕ) : Prop :=
  ∃ e : ℕ, e ≤ t ∧ coordinateBundleMinimalExactification m n s e

theorem conclusion_coordinatebundle_arbitrary_completion_sharp_lower_bound_defect_eq_audit_gap
    (m n s : ℕ) : coordinateBundleDefect m n s = coordinateBundleAuditGap m n s :=
  rfl

theorem conclusion_coordinatebundle_arbitrary_completion_sharp_lower_bound_exactifiable_at_gap
    (m n s : ℕ) :
    conclusion_coordinatebundle_arbitrary_completion_sharp_lower_bound_exactifiable m n s
      (coordinateBundleAuditGap m n s) := by
  refine ⟨coordinateBundleDefect m n s, ?_, rfl⟩
  simp [conclusion_coordinatebundle_arbitrary_completion_sharp_lower_bound_defect_eq_audit_gap]

/-- Paper label:
`thm:conclusion-coordinatebundle-arbitrary-completion-sharp-lower-bound`. -/
theorem paper_conclusion_coordinatebundle_arbitrary_completion_sharp_lower_bound
    (m n s t : ℕ) :
    conclusion_coordinatebundle_arbitrary_completion_sharp_lower_bound_residual_gap m n s t =
        max (coordinateBundleAuditGap m n s - t) 0 ∧
      (conclusion_coordinatebundle_arbitrary_completion_sharp_lower_bound_exactifiable m n s t →
        coordinateBundleAuditGap m n s ≤ t) := by
  refine ⟨?_, ?_⟩
  · simp [conclusion_coordinatebundle_arbitrary_completion_sharp_lower_bound_residual_gap]
  · intro hExact
    rcases hExact with ⟨e, he_le, hMin⟩
    rcases paper_conclusion_coordinatebundle_all_minimal_exactifications_spanning_trees m n s with
      ⟨_, hExactIff, hTreeEdges⟩
    have hTree : coordinateBundleSpanningTreeEdgeCount m n s e := (hExactIff e).mp hMin
    have heq : e = coordinateBundleDefect m n s := hTreeEdges e hTree
    calc
      coordinateBundleAuditGap m n s = coordinateBundleDefect m n s := by
        symm
        exact
          conclusion_coordinatebundle_arbitrary_completion_sharp_lower_bound_defect_eq_audit_gap
            m n s
      _ = e := heq.symm
      _ ≤ t := he_le

end Omega.Conclusion
