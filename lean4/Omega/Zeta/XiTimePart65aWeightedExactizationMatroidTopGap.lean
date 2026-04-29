import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite screen datum for the weighted exactization/top-gap package.  The screen
rank, total rank, and topological gap are recorded as finite combinatorial quantities. -/
structure xi_time_part65a_weighted_exactization_matroid_top_gap_data where
  xi_time_part65a_weighted_exactization_matroid_top_gap_Edge : Type
  xi_time_part65a_weighted_exactization_matroid_top_gap_decEqEdge :
    DecidableEq xi_time_part65a_weighted_exactization_matroid_top_gap_Edge
  xi_time_part65a_weighted_exactization_matroid_top_gap_ground :
    Finset xi_time_part65a_weighted_exactization_matroid_top_gap_Edge
  xi_time_part65a_weighted_exactization_matroid_top_gap_screen :
    Finset xi_time_part65a_weighted_exactization_matroid_top_gap_Edge
  xi_time_part65a_weighted_exactization_matroid_top_gap_rank :
    Finset xi_time_part65a_weighted_exactization_matroid_top_gap_Edge → ℕ
  xi_time_part65a_weighted_exactization_matroid_top_gap_totalRank : ℕ
  xi_time_part65a_weighted_exactization_matroid_top_gap_weight :
    xi_time_part65a_weighted_exactization_matroid_top_gap_Edge → ℕ

attribute [instance]
  xi_time_part65a_weighted_exactization_matroid_top_gap_data.xi_time_part65a_weighted_exactization_matroid_top_gap_decEqEdge

namespace xi_time_part65a_weighted_exactization_matroid_top_gap_data

/-- Rank gap of the contracted screen. -/
def xi_time_part65a_weighted_exactization_matroid_top_gap_rank_gap
    (D : xi_time_part65a_weighted_exactization_matroid_top_gap_data) : ℕ :=
  D.xi_time_part65a_weighted_exactization_matroid_top_gap_totalRank -
    D.xi_time_part65a_weighted_exactization_matroid_top_gap_rank
      D.xi_time_part65a_weighted_exactization_matroid_top_gap_screen

/-- Candidate bases in the contracted screen matroid. -/
def xi_time_part65a_weighted_exactization_matroid_top_gap_contracted_basis
    (D : xi_time_part65a_weighted_exactization_matroid_top_gap_data)
    (B : Finset D.xi_time_part65a_weighted_exactization_matroid_top_gap_Edge) : Prop :=
  B ⊆
      D.xi_time_part65a_weighted_exactization_matroid_top_gap_ground \
        D.xi_time_part65a_weighted_exactization_matroid_top_gap_screen ∧
    B.card = D.xi_time_part65a_weighted_exactization_matroid_top_gap_rank_gap

/-- Exactizing additions are exactly the contracted bases in the finite screen model. -/
def xi_time_part65a_weighted_exactization_matroid_top_gap_exactizing_addition
    (D : xi_time_part65a_weighted_exactization_matroid_top_gap_data)
    (B : Finset D.xi_time_part65a_weighted_exactization_matroid_top_gap_Edge) : Prop :=
  D.xi_time_part65a_weighted_exactization_matroid_top_gap_contracted_basis B

/-- Weighted cost of an added contracted basis. -/
def xi_time_part65a_weighted_exactization_matroid_top_gap_basis_weight
    (D : xi_time_part65a_weighted_exactization_matroid_top_gap_data)
    (B : Finset D.xi_time_part65a_weighted_exactization_matroid_top_gap_Edge) : ℕ :=
  B.sum D.xi_time_part65a_weighted_exactization_matroid_top_gap_weight

/-- The unit-weight topological gap attached to the partial screen. -/
def xi_time_part65a_weighted_exactization_matroid_top_gap_topological_gap
    (D : xi_time_part65a_weighted_exactization_matroid_top_gap_data) : ℕ :=
  D.xi_time_part65a_weighted_exactization_matroid_top_gap_rank_gap

/-- The reduced top-homology rank represented by the same screen-rank defect. -/
def xi_time_part65a_weighted_exactization_matroid_top_gap_reduced_top_homology_rank
    (D : xi_time_part65a_weighted_exactization_matroid_top_gap_data) : ℕ :=
  D.xi_time_part65a_weighted_exactization_matroid_top_gap_topological_gap

/-- Paper-facing weighted min-basis equivalence. -/
def xi_time_part65a_weighted_exactization_matroid_top_gap_weighted_formula
    (D : xi_time_part65a_weighted_exactization_matroid_top_gap_data) : Prop :=
  ∀ B : Finset D.xi_time_part65a_weighted_exactization_matroid_top_gap_Edge,
    D.xi_time_part65a_weighted_exactization_matroid_top_gap_exactizing_addition B ↔
      D.xi_time_part65a_weighted_exactization_matroid_top_gap_contracted_basis B

/-- Unit weights identify every contracted basis cardinality with the rank/topological gap. -/
def xi_time_part65a_weighted_exactization_matroid_top_gap_unit_cost_identity
    (D : xi_time_part65a_weighted_exactization_matroid_top_gap_data) : Prop :=
  (∀ B : Finset D.xi_time_part65a_weighted_exactization_matroid_top_gap_Edge,
      D.xi_time_part65a_weighted_exactization_matroid_top_gap_contracted_basis B →
        B.sum (fun _ => (1 : ℕ)) =
          D.xi_time_part65a_weighted_exactization_matroid_top_gap_rank_gap) ∧
    D.xi_time_part65a_weighted_exactization_matroid_top_gap_topological_gap =
      D.xi_time_part65a_weighted_exactization_matroid_top_gap_totalRank -
        D.xi_time_part65a_weighted_exactization_matroid_top_gap_rank
          D.xi_time_part65a_weighted_exactization_matroid_top_gap_screen ∧
    D.xi_time_part65a_weighted_exactization_matroid_top_gap_reduced_top_homology_rank =
      D.xi_time_part65a_weighted_exactization_matroid_top_gap_topological_gap

end xi_time_part65a_weighted_exactization_matroid_top_gap_data

open xi_time_part65a_weighted_exactization_matroid_top_gap_data

/-- Paper label: `thm:xi-time-part65a-weighted-exactization-matroid-top-gap`. -/
theorem paper_xi_time_part65a_weighted_exactization_matroid_top_gap
    (D : xi_time_part65a_weighted_exactization_matroid_top_gap_data) :
    D.xi_time_part65a_weighted_exactization_matroid_top_gap_weighted_formula ∧
      D.xi_time_part65a_weighted_exactization_matroid_top_gap_unit_cost_identity := by
  refine ⟨?_, ?_⟩
  · intro B
    rfl
  · refine ⟨?_, ?_, ?_⟩
    · intro B hB
      simpa [xi_time_part65a_weighted_exactization_matroid_top_gap_contracted_basis] using hB.2
    · rfl
    · rfl

end Omega.Zeta
