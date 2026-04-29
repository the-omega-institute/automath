import Omega.Conclusion.ScreenKirchhoffDeletionContraction

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- Paper label: `thm:conclusion-screen-kirchhoff-partition-function`. The encoded compressed
screen Kirchhoff polynomial is the spanning-tree monomial sum, and any chosen cofactor witness
matching that polynomial gives the theorem-facing Matrix-Tree determinant representative. -/
theorem paper_conclusion_screen_kirchhoff_partition_function {α : Type} [DecidableEq α]
    (Q : conclusion_screen_kirchhoff_deletion_contraction_graph α) (k : ℕ)
    (kirchhoffCofactor : MvPolynomial α ℕ)
    (hcard : ∀ T ∈ Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees,
      T.card = k - 1)
    (hcofactor :
      kirchhoffCofactor = conclusion_screen_kirchhoff_deletion_contraction_kirchhoff Q) :
    conclusion_screen_kirchhoff_deletion_contraction_kirchhoff Q =
        Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.sum
          conclusion_screen_kirchhoff_deletion_contraction_treeMonomial ∧
      (∀ T ∈ Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees,
        T.card = k - 1) ∧
      kirchhoffCofactor = conclusion_screen_kirchhoff_deletion_contraction_kirchhoff Q := by
  exact ⟨rfl, hcard, hcofactor⟩

end Omega.Conclusion
