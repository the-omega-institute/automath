import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The two compressed exactization edges in the minimal rank-two screen model. -/
abbrev conclusion_screen_optimal_exactization_exchange_connected_Edge := Fin 2

/-- The optimal exactization clusters in the concrete rank-two screen model are the singleton
edge sets. -/
def conclusion_screen_optimal_exactization_exchange_connected_optimal
    (T : Finset conclusion_screen_optimal_exactization_exchange_connected_Edge) : Prop :=
  T.card = 1

/-- A single admissible exchange replaces one selected edge by one unselected edge. -/
def conclusion_screen_optimal_exactization_exchange_connected_singleExchange
    (U V : Finset conclusion_screen_optimal_exactization_exchange_connected_Edge) : Prop :=
  ∃ e ∈ U, ∃ f ∉ U, V = insert f (U.erase e)

/-- The exchange graph on optimal exactization clusters allows the identity move and one-edge
exchanges. -/
def conclusion_screen_optimal_exactization_exchange_connected_reachable
    (U V : Finset conclusion_screen_optimal_exactization_exchange_connected_Edge) : Prop :=
  U = V ∨ conclusion_screen_optimal_exactization_exchange_connected_singleExchange U V

/-- Every concrete optimal cluster has the screen rank gap cardinality `k - 1 = 1`. -/
def conclusion_screen_optimal_exactization_exchange_connected_all_minimal_optima_cardinality :
    Prop :=
  ∀ T : Finset conclusion_screen_optimal_exactization_exchange_connected_Edge,
    conclusion_screen_optimal_exactization_exchange_connected_optimal T → T.card = 1

/-- Any two concrete optimal clusters are connected by at most one basis exchange. -/
def conclusion_screen_optimal_exactization_exchange_connected_exchange_connected : Prop :=
  ∀ U V : Finset conclusion_screen_optimal_exactization_exchange_connected_Edge,
    conclusion_screen_optimal_exactization_exchange_connected_optimal U →
      conclusion_screen_optimal_exactization_exchange_connected_optimal V →
        conclusion_screen_optimal_exactization_exchange_connected_reachable U V

/-- Paper label: `prop:conclusion-screen-optimal-exactization-exchange-connected`. -/
theorem paper_conclusion_screen_optimal_exactization_exchange_connected :
    conclusion_screen_optimal_exactization_exchange_connected_all_minimal_optima_cardinality ∧
      conclusion_screen_optimal_exactization_exchange_connected_exchange_connected := by
  classical
  refine ⟨?_, ?_⟩
  · intro T hT
    exact hT
  · intro U V hU hV
    rcases Finset.card_eq_one.mp hU with ⟨u, rfl⟩
    rcases Finset.card_eq_one.mp hV with ⟨v, rfl⟩
    by_cases huv : u = v
    · left
      simp [huv]
    · right
      have hvu : v ≠ u := fun hvu => huv hvu.symm
      refine ⟨u, by simp, v, by simp [hvu], ?_⟩
      simp

end Omega.Conclusion
