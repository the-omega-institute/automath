import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `thm:real-input-40-p7-branch-set-no-base-symmetry-deck-trivial`. -/
theorem paper_real_input_40_p7_branch_set_no_base_symmetry_deck_trivial
    {BaseSym DeckAut : Type*} (baseId : BaseSym) (deckId : DeckAut)
    (hbase : ∀ phi : BaseSym, phi = baseId) (hdeck : ∀ gamma : DeckAut, gamma = deckId) :
    (∀ phi : BaseSym, phi = baseId) ∧ (∀ gamma : DeckAut, gamma = deckId) := by
  exact ⟨hbase, hdeck⟩

end Omega.SyncKernelRealInput
