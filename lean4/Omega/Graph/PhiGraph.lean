import Omega.Core.Word
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Graph

abbrev PhiState (m : Nat) := Word (m - 1)
abbrev PhiEdge (m : Nat) := PhiState m × Bool

/-- Number of states in the explicit sofic graph `G_m`.
    def:G_m -/
theorem phiState_card (m : Nat) :
    Fintype.card (PhiState m) = 2 ^ (m - 1) := by
  simp [PhiState, Word]

/-- Number of edges in the explicit sofic graph `G_m`.
    thm:Phi_m-sofic-graph -/
theorem phiEdge_card (m : Nat) (hm : 1 ≤ m) :
    Fintype.card (PhiEdge m) = 2 ^ m := by
  change Fintype.card (Word (m - 1) × Bool) = 2 ^ m
  calc
    Fintype.card (Word (m - 1) × Bool) = 2 ^ (m - 1) * 2 := by simp [Word]
    _ = 2 ^ ((m - 1) + 1) := by rw [pow_succ']; ring
    _ = 2 ^ m := by rw [Nat.sub_add_cancel hm]

/-- Every state of `G_m` has outdegree two.
    thm:Phi_m-sofic-graph -/
theorem phiGraph_outdegree_two (m : Nat) (v : PhiState m) :
    Fintype.card {e : PhiEdge m // e.1 = v} = 2 := by
  classical
  let e : {e : PhiEdge m // e.1 = v} ≃ Bool :=
    { toFun := fun x => x.1.2
      invFun := fun b => ⟨(v, b), rfl⟩
      left_inv := by
        intro x
        rcases x with ⟨⟨v', b⟩, hx⟩
        cases hx
        rfl
      right_inv := by
        intro b
        rfl }
  exact Fintype.card_congr e

/-- Paper: `thm:Phi_m-sofic-graph`. -/
theorem paper_phi_m_sofic_graph (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (Omega.Graph.PhiEdge m) = 2 ^ m ∧
    (∀ v : Omega.Graph.PhiState m,
      Fintype.card {e : Omega.Graph.PhiEdge m // e.1 = v} = 2) := by
  exact ⟨phiEdge_card m hm, phiGraph_outdegree_two m⟩

end Omega.Graph
