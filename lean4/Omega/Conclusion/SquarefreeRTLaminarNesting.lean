import Mathlib.Tactic
import Omega.SPG.CutFunctionSubmodular

namespace Omega.Conclusion

open Finset
open Omega.SPG.CutFunctionSubmodular

/-- Concrete laminar min-cut data for a squarefree RT family. Each level of the laminar boundary
chain comes with a selected minimizer, and the selected chain is already order-compatible. The
submodularity theorem from `Omega.SPG.CutFunctionSubmodular` supplies closure of the whole
minimizer family under intersections and unions. -/
structure SquarefreeRTLaminarNestingData where
  V : Type
  instFintypeV : Fintype V
  instDecidableEqV : DecidableEq V
  E : Type
  edges : Finset E
  endpoints : E → V × V
  weight : E → ℕ
  depth : ℕ
  boundary : Fin depth → Finset V
  selected : Fin depth → Finset V
  boundary_le_selected : ∀ i, boundary i ⊆ selected i
  boundaryNested : ∀ {i j : Fin depth}, i ≤ j → boundary i ⊆ boundary j
  selectedNested : ∀ {i j : Fin depth}, i ≤ j → selected i ⊆ selected j
  selectedMinimal :
    ∀ i T,
      boundary i ⊆ T →
      cutWeight edges endpoints weight (selected i) ≤ cutWeight edges endpoints weight T

attribute [instance] SquarefreeRTLaminarNestingData.instFintypeV
attribute [instance] SquarefreeRTLaminarNestingData.instDecidableEqV

namespace SquarefreeRTLaminarNestingData

/-- The cut objective at the current RT boundary layer. -/
def cutValue (D : SquarefreeRTLaminarNestingData) (S : Finset D.V) : ℕ :=
  cutWeight D.edges D.endpoints D.weight S

/-- `S` is a minimizer for layer `i` if it contains the prescribed boundary data and has no larger
cut value than any other admissible set. -/
def IsMinimizer (D : SquarefreeRTLaminarNestingData) (i : Fin D.depth) (S : Finset D.V) : Prop :=
  D.boundary i ⊆ S ∧ ∀ T, D.boundary i ⊆ T → D.cutValue S ≤ D.cutValue T

/-- The minimizer family is closed under intersections and unions at each boundary layer. -/
def closedUnderIntersectionUnion (D : SquarefreeRTLaminarNestingData) : Prop :=
  ∀ i S T,
    D.IsMinimizer i S →
      D.IsMinimizer i T →
        D.IsMinimizer i (S ∩ T) ∧ D.IsMinimizer i (S ∪ T)

/-- A selection is order-compatible if it respects the nesting order on the laminar boundary data. -/
def OrderCompatibleSelection (D : SquarefreeRTLaminarNestingData)
    (M : Fin D.depth → Finset D.V) : Prop :=
  ∀ {i j : Fin D.depth}, i ≤ j → M i ⊆ M j

/-- Existence of a monotone chain of minimizers compatible with the laminar order. -/
def existsOrderCompatibleSelection (D : SquarefreeRTLaminarNestingData) : Prop :=
  ∃ M : Fin D.depth → Finset D.V, D.OrderCompatibleSelection M ∧ ∀ i, D.IsMinimizer i (M i)

/-- The chosen support at each level is the canonical support used by the wrapper. -/
def canonicalSupport (D : SquarefreeRTLaminarNestingData) (i : Fin D.depth) : Finset D.V :=
  D.selected i

/-- The selected supports are bona fide minimizers, hence give a canonical laminar support chain. -/
def canonicalSupports (D : SquarefreeRTLaminarNestingData) : Prop :=
  ∀ i, D.IsMinimizer i (D.canonicalSupport i)

lemma selected_isMinimizer (D : SquarefreeRTLaminarNestingData) (i : Fin D.depth) :
    D.IsMinimizer i (D.selected i) := by
  refine ⟨D.boundary_le_selected i, ?_⟩
  intro T hT
  exact D.selectedMinimal i T hT

lemma minimizer_closed_under_intersection_union (D : SquarefreeRTLaminarNestingData)
    (i : Fin D.depth) (S T : Finset D.V) (hS : D.IsMinimizer i S) (hT : D.IsMinimizer i T) :
    D.IsMinimizer i (S ∩ T) ∧ D.IsMinimizer i (S ∪ T) := by
  have hBoundary_inter : D.boundary i ⊆ S ∩ T := by
    intro v hv
    exact mem_inter.mpr ⟨hS.1 hv, hT.1 hv⟩
  have hBoundary_union : D.boundary i ⊆ S ∪ T := by
    intro v hv
    exact mem_union.mpr <| Or.inl (hS.1 hv)
  have hST : D.cutValue S = D.cutValue T := by
    exact le_antisymm (hS.2 T hT.1) (hT.2 S hS.1)
  have hInter_ge : D.cutValue S ≤ D.cutValue (S ∩ T) := hS.2 (S ∩ T) hBoundary_inter
  have hUnion_ge : D.cutValue T ≤ D.cutValue (S ∪ T) := hT.2 (S ∪ T) hBoundary_union
  have hsub :
      D.cutValue (S ∪ T) + D.cutValue (S ∩ T) ≤ D.cutValue S + D.cutValue T := by
    simpa [SquarefreeRTLaminarNestingData.cutValue] using
      cutWeight_submodular D.edges D.endpoints D.weight S T
  have hsum_ge : D.cutValue S + D.cutValue S ≤ D.cutValue (S ∪ T) + D.cutValue (S ∩ T) := by
    have htmp : D.cutValue T + D.cutValue S ≤ D.cutValue (S ∪ T) + D.cutValue (S ∩ T) :=
      Nat.add_le_add hUnion_ge hInter_ge
    simpa [hST, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htmp
  have hsum_le : D.cutValue (S ∪ T) + D.cutValue (S ∩ T) ≤ D.cutValue S + D.cutValue S := by
    simpa [hST] using hsub
  have hUnion_eq : D.cutValue (S ∪ T) = D.cutValue S := by
    omega
  have hInter_eq : D.cutValue (S ∩ T) = D.cutValue S := by
    omega
  refine ⟨?_, ?_⟩
  · refine ⟨hBoundary_inter, ?_⟩
    intro U hU
    simpa [hInter_eq] using hS.2 U hU
  · refine ⟨hBoundary_union, ?_⟩
    intro U hU
    simpa [hUnion_eq] using hS.2 U hU

end SquarefreeRTLaminarNestingData

open SquarefreeRTLaminarNestingData

/-- For nested squarefree RT boundary data, submodularity keeps minimizers closed under
intersections and unions, the selected minimizers already form an order-compatible chain, and
those selected supports serve as the canonical support package.
    thm:conclusion-squarefree-rt-laminar-nesting -/
theorem paper_conclusion_squarefree_rt_laminar_nesting (D : SquarefreeRTLaminarNestingData) :
    D.closedUnderIntersectionUnion ∧ D.existsOrderCompatibleSelection ∧ D.canonicalSupports := by
  refine ⟨?_, ?_, ?_⟩
  · intro i S T hS hT
    exact D.minimizer_closed_under_intersection_union i S T hS hT
  · refine ⟨D.selected, ?_, ?_⟩
    · intro i j hij
      exact D.selectedNested hij
    · intro i
      exact D.selected_isMinimizer i
  · intro i
    exact D.selected_isMinimizer i

end Omega.Conclusion
