import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Graph.LabeledGraph

namespace Omega.Graph

abbrev LabeledPath {V : Type*} [Fintype V] (step : V → Bool → V) (w : Fin n → Bool) :=
  {p : Fin (n + 1) → V // ∀ i : Fin n, p i.succ = step (p i.castSucc) (w i)}

/-- A labeled path is determined by its initial vertex.
    cor:Phi_m-entropy-no-drop -/
theorem labeledPath_initial_injective {V : Type*} [Fintype V] [DecidableEq V]
    (step : V → Bool → V) (w : Fin n → Bool) :
    Function.Injective (fun p : LabeledPath step w => p.1 0) := by
  intro p q h0
  rcases p with ⟨p, hp⟩
  rcases q with ⟨q, hq⟩
  apply Subtype.ext
  funext i
  induction i using Fin.induction with
  | zero => simpa using h0
  | succ i ih =>
      simpa [hp i, hq i] using congrArg (fun v => step v (w i)) ih

/-- The number of deterministic lifts is bounded by the number of states.
    cor:Phi_m-entropy-no-drop -/
theorem labeledPath_card_le_state_card {V : Type*} [Fintype V] [DecidableEq V]
    (step : V → Bool → V) (w : Fin n → Bool) :
    Fintype.card (LabeledPath step w) ≤ Fintype.card V := by
  simpa using Fintype.card_le_of_injective (fun p : LabeledPath step w => p.1 0)
    (labeledPath_initial_injective step w)

-- Phase R605: Labeled path lift bound via AcceptsSeq
-- ══════════════════════════════════════════════════════════════

/-- The number of starting states that accept a word is bounded by the state count.
    cor:Phi_m-entropy-no-drop -/
theorem labeledPath_count_le_states (G : LabeledGraph σ α) [Fintype σ] [DecidableEq σ]
    (w : Fin m → α) (hdec : DecidablePred (fun s => AcceptsSeq G s w)) :
    (Finset.univ.filter (fun s => AcceptsSeq G s w)).card ≤ Fintype.card σ :=
  Finset.card_filter_le _ _

/-- Paper seeds: power-of-2 lift bounds.
    cor:Phi_m-entropy-no-drop -/
theorem paper_labeled_path_lift_bound :
    (2 ^ (2 - 1) = 2) ∧
    (2 ^ (3 - 1) = 4) ∧
    (2 ^ (4 - 1) = 8) := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end Omega.Graph
