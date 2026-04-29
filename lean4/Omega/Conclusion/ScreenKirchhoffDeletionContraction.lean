import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset
open scoped BigOperators

variable {α : Type} [DecidableEq α]

/-- A compressed screen graph is encoded by its finite family of spanning-tree edge sets. -/
structure conclusion_screen_kirchhoff_deletion_contraction_graph (α : Type)
    [DecidableEq α] where
  conclusion_screen_kirchhoff_deletion_contraction_spanningTrees : Finset (Finset α)

/-- The monomial attached to one spanning tree. -/
noncomputable def conclusion_screen_kirchhoff_deletion_contraction_treeMonomial
    (T : Finset α) : MvPolynomial α ℕ :=
  T.prod fun e => MvPolynomial.X e

/-- The Kirchhoff polynomial of the compressed screen graph. -/
noncomputable def conclusion_screen_kirchhoff_deletion_contraction_kirchhoff
    (Q : conclusion_screen_kirchhoff_deletion_contraction_graph α) : MvPolynomial α ℕ :=
  Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.sum
    conclusion_screen_kirchhoff_deletion_contraction_treeMonomial

/-- Delete the edge `e` by keeping the spanning trees that avoid it. -/
def conclusion_screen_kirchhoff_deletion_contraction_delete
    (Q : conclusion_screen_kirchhoff_deletion_contraction_graph α) (e : α) :
    conclusion_screen_kirchhoff_deletion_contraction_graph α where
  conclusion_screen_kirchhoff_deletion_contraction_spanningTrees :=
    Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.filter fun T => e ∉ T

/-- Contract the edge `e` by erasing it from the spanning trees that contain it. -/
def conclusion_screen_kirchhoff_deletion_contraction_contract
    (Q : conclusion_screen_kirchhoff_deletion_contraction_graph α) (e : α) :
    conclusion_screen_kirchhoff_deletion_contraction_graph α where
  conclusion_screen_kirchhoff_deletion_contraction_spanningTrees :=
    (Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.filter fun T => e ∈ T).image
      fun T => T.erase e

lemma conclusion_screen_kirchhoff_deletion_contraction_treeMonomial_erase
    (T : Finset α) {e : α} (he : e ∈ T) :
    conclusion_screen_kirchhoff_deletion_contraction_treeMonomial T =
      MvPolynomial.X e *
        conclusion_screen_kirchhoff_deletion_contraction_treeMonomial (T.erase e) := by
  rw [← insert_erase he]
  simp [conclusion_screen_kirchhoff_deletion_contraction_treeMonomial, Finset.prod_insert, mul_comm]

lemma conclusion_screen_kirchhoff_deletion_contraction_contract_sum
    (Q : conclusion_screen_kirchhoff_deletion_contraction_graph α) (e : α) :
    (Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.filter fun T => e ∈ T).sum
        conclusion_screen_kirchhoff_deletion_contraction_treeMonomial =
      MvPolynomial.X e *
        conclusion_screen_kirchhoff_deletion_contraction_kirchhoff
          (conclusion_screen_kirchhoff_deletion_contraction_contract Q e) := by
  calc
    (Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.filter fun T => e ∈ T).sum
        conclusion_screen_kirchhoff_deletion_contraction_treeMonomial =
      (Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.filter fun T => e ∈ T).sum
        (fun T =>
          MvPolynomial.X e *
            conclusion_screen_kirchhoff_deletion_contraction_treeMonomial (T.erase e)) := by
        refine sum_congr rfl ?_
        intro T hT
        exact conclusion_screen_kirchhoff_deletion_contraction_treeMonomial_erase T
          ((mem_filter.mp hT).2)
    _ = MvPolynomial.X e *
        (Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.filter fun T => e ∈ T).sum
          (fun T => conclusion_screen_kirchhoff_deletion_contraction_treeMonomial (T.erase e)) := by
        rw [mul_sum]
    _ = MvPolynomial.X e *
        ((Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.filter
            fun T => e ∈ T).image fun T => T.erase e).sum
          conclusion_screen_kirchhoff_deletion_contraction_treeMonomial := by
        congr 1
        symm
        refine sum_image ?_
        intro T hT T' hT' hEq
        exact Finset.erase_injOn' e ((mem_filter.mp hT).2) ((mem_filter.mp hT').2) hEq
    _ = MvPolynomial.X e *
        conclusion_screen_kirchhoff_deletion_contraction_kirchhoff
          (conclusion_screen_kirchhoff_deletion_contraction_contract Q e) := by
        rfl

/-- Paper label: `thm:conclusion-screen-kirchhoff-deletion-contraction`. Splitting the encoded
spanning-tree family by whether it contains `e` yields the usual deletion-contraction recursion for
the prefixed Kirchhoff polynomial. -/
theorem paper_conclusion_screen_kirchhoff_deletion_contraction
    [Fintype α] (Q : conclusion_screen_kirchhoff_deletion_contraction_graph α) (e : α) :
    conclusion_screen_kirchhoff_deletion_contraction_kirchhoff Q =
      conclusion_screen_kirchhoff_deletion_contraction_kirchhoff
          (conclusion_screen_kirchhoff_deletion_contraction_delete Q e) +
        MvPolynomial.X e *
          conclusion_screen_kirchhoff_deletion_contraction_kirchhoff
            (conclusion_screen_kirchhoff_deletion_contraction_contract Q e) := by
  calc
    conclusion_screen_kirchhoff_deletion_contraction_kirchhoff Q =
        (Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.filter fun T => e ∉ T).sum
            conclusion_screen_kirchhoff_deletion_contraction_treeMonomial +
          (Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.filter
              fun T => e ∈ T).sum
            conclusion_screen_kirchhoff_deletion_contraction_treeMonomial := by
        simpa [conclusion_screen_kirchhoff_deletion_contraction_kirchhoff, add_comm] using
          (Finset.sum_filter_add_sum_filter_not
            Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees
            (fun T => e ∈ T)
            conclusion_screen_kirchhoff_deletion_contraction_treeMonomial).symm
    _ =
        conclusion_screen_kirchhoff_deletion_contraction_kirchhoff
            (conclusion_screen_kirchhoff_deletion_contraction_delete Q e) +
          (Q.conclusion_screen_kirchhoff_deletion_contraction_spanningTrees.filter
              fun T => e ∈ T).sum
            conclusion_screen_kirchhoff_deletion_contraction_treeMonomial := by
        rfl
    _ =
        conclusion_screen_kirchhoff_deletion_contraction_kirchhoff
            (conclusion_screen_kirchhoff_deletion_contraction_delete Q e) +
          MvPolynomial.X e *
            conclusion_screen_kirchhoff_deletion_contraction_kirchhoff
              (conclusion_screen_kirchhoff_deletion_contraction_contract Q e) := by
          rw [conclusion_screen_kirchhoff_deletion_contraction_contract_sum]

end Omega.Conclusion
