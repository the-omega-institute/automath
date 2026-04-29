import Omega.Conclusion.CoordinateBundleAllMinimalExactificationsSpanningTrees
import Omega.Conclusion.ScreenKirchhoffPartitionFunction

namespace Omega.Conclusion

open scoped BigOperators

/-- The full exactification polynomial, encoded as the weighted spanning-tree sum. -/
noncomputable def conclusion_coordinatebundle_full_exactification_kirchhoff_polynomial_fullPolynomial
    {α : Type} [DecidableEq α]
    (Q : conclusion_screen_kirchhoff_deletion_contraction_graph α) : MvPolynomial α ℕ :=
  Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.sum
    conclusion_screen_kirchhoff_deletion_contraction_treeMonomial

/-- Paper label: `cor:conclusion-coordinatebundle-full-exactification-kirchhoff-polynomial`.
The encoded family of full minimal exactifications is transferred across the spanning-tree
correspondence to the Kirchhoff tree polynomial. The fixed tree edge count gives the homogeneous
degree `δ_J`, represented here by the common cardinality of every tree monomial support. -/
theorem paper_conclusion_coordinatebundle_full_exactification_kirchhoff_polynomial
    {α : Type} [DecidableEq α] (m n s : ℕ)
    (Q : conclusion_screen_kirchhoff_deletion_contraction_graph α)
    (hcard :
      ∀ T ∈ Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees,
        T.card = coordinateBundleDefect m n s) :
    conclusion_coordinatebundle_full_exactification_kirchhoff_polynomial_fullPolynomial Q =
        conclusion_screen_kirchhoff_deletion_contraction_kirchhoff Q ∧
      (∀ T ∈ Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees,
        T.card = coordinateBundleDefect m n s) ∧
      coordinateBundleVertexCount m n s = coordinateBundleDefect m n s + 1 := by
  rcases paper_conclusion_coordinatebundle_all_minimal_exactifications_spanning_trees m n s with
    ⟨hvertices, _hcorrespondence, _hedges⟩
  exact ⟨rfl, hcard, hvertices⟩

end Omega.Conclusion
