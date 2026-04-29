import Omega.Conclusion.ScreenKirchhoffDeletionContraction

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-screen-minimal-exact-audit-tree-kirchhoff-count`. Minimal exact
audit packages are precisely the encoded spanning trees; the common tree edge count and total
Kirchhoff tree count are therefore inherited from the stored spanning-tree family. -/
theorem paper_conclusion_screen_minimal_exact_audit_tree_kirchhoff_count {alpha : Type}
    [DecidableEq alpha] (Q : conclusion_screen_kirchhoff_deletion_contraction_graph alpha)
    (k tau : Nat) (minimalAudit : Finset alpha → Prop)
    (hTree : ∀ A,
      minimalAudit A ↔ A ∈ Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees)
    (hCard : ∀ A,
      A ∈ Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees → A.card = k - 1)
    (hCount : Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.card = tau) :
    (∀ A,
      minimalAudit A ↔ A ∈ Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees) ∧
      (∀ A, minimalAudit A → A.card = k - 1) ∧
      Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.card = tau := by
  refine ⟨hTree, ?_, hCount⟩
  intro A hA
  exact hCard A ((hTree A).mp hA)

end Omega.Conclusion
