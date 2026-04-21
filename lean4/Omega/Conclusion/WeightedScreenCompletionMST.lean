import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset
open scoped BigOperators

variable {E : Type*} [DecidableEq E]

/-- Total cost of a weighted completion on the quotient graph. -/
def weightedScreenCompletionCost (cost : E → ℕ) (T : Finset E) : ℕ :=
  T.sum cost

/-- Feasible completions are the edge sets whose lift reconnects the partial screen. -/
def weightedScreenCompletionOptimal (feasible : Finset E → Prop) (cost : E → ℕ)
    (T : Finset E) : Prop :=
  feasible T ∧ ∀ U : Finset E, feasible U → weightedScreenCompletionCost cost T ≤
    weightedScreenCompletionCost cost U

/-- Inclusion-minimal feasible completions are the ones from which no chosen edge can be removed
while preserving feasibility. -/
def weightedScreenCompletionInclusionMinimal (feasible : Finset E → Prop) (T : Finset E) : Prop :=
  ∀ e ∈ T, ¬ feasible (T.erase e)

/-- A minimum spanning tree of the quotient graph is a tree with minimum total edge cost. -/
def quotientMinimumSpanningTree (tree : Finset E → Prop) (cost : E → ℕ) (T : Finset E) : Prop :=
  tree T ∧ ∀ U : Finset E, tree U → weightedScreenCompletionCost cost T ≤
    weightedScreenCompletionCost cost U

/-- Any cost-optimal completion can be compared against a spanning tree of the quotient graph, and
inclusion-minimal cost-optimal completions are exactly minimum spanning trees. The pruning step is
encoded by `hPrune`, while `hDelete` records that every non-tree feasible completion contains a
deletable cycle edge.
    thm:xi-time-part65f-weighted-screen-completion-mst -/
theorem paper_xi_time_part65f_weighted_screen_completion_mst
    (feasible tree : Finset E → Prop) (cost : E → ℕ)
    (hTreeFeasible : ∀ T : Finset E, tree T → feasible T)
    (hPrune : ∀ T : Finset E, feasible T →
      ∃ Ttr : Finset E, Ttr ⊆ T ∧ tree Ttr ∧
        weightedScreenCompletionCost cost Ttr ≤ weightedScreenCompletionCost cost T)
    (hDelete : ∀ T : Finset E, feasible T → ¬ tree T →
      ∃ e ∈ T, feasible (T.erase e)) :
    (∀ T : Finset E, feasible T →
      ∃ Ttr : Finset E, Ttr ⊆ T ∧ tree Ttr ∧
        weightedScreenCompletionCost cost Ttr ≤ weightedScreenCompletionCost cost T) ∧
      (∀ T : Finset E, quotientMinimumSpanningTree tree cost T →
        weightedScreenCompletionOptimal feasible cost T) ∧
      ∀ T : Finset E, weightedScreenCompletionOptimal feasible cost T →
        weightedScreenCompletionInclusionMinimal feasible T →
          quotientMinimumSpanningTree tree cost T := by
  refine ⟨hPrune, ?_, ?_⟩
  · intro T hmst
    rcases hmst with ⟨hTreeT, hminT⟩
    refine ⟨hTreeFeasible T hTreeT, ?_⟩
    intro U hU
    rcases hPrune U hU with ⟨Utr, hsub, hTreeUtr, hcostUtr⟩
    exact (hminT Utr hTreeUtr).trans hcostUtr
  · intro T hopt hminimal
    rcases hopt with ⟨hfeasT, hoptT⟩
    have htreeT : tree T := by
      by_contra hnotTree
      rcases hDelete T hfeasT hnotTree with ⟨e, heT, herase⟩
      exact (hminimal e heT) herase
    refine ⟨htreeT, ?_⟩
    intro U hTreeU
    exact hoptT U (hTreeFeasible U hTreeU)

end Omega.Conclusion
