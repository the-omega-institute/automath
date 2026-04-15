import Omega.Graph.PhiGraph

namespace Omega.Folding

/-- Chapter-facing wrapper for the explicit `Y_m` sofic presentation.
    prop:Y_m-sofic -/
theorem paper_Ym_sofic (m : Nat) (hm : 1 ≤ m) :
    Fintype.card (Omega.Graph.PhiState m) = 2 ^ (m - 1) ∧
      Fintype.card (Omega.Graph.PhiEdge m) = 2 ^ m ∧
      (∀ v : Omega.Graph.PhiState m,
        Fintype.card {e : Omega.Graph.PhiEdge m // e.1 = v} = 2) := by
  refine ⟨Omega.Graph.phiState_card m, ?_⟩
  exact Omega.Graph.paper_phi_m_sofic_graph m hm

end Omega.Folding
