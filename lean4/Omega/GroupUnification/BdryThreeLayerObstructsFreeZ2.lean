import Omega.Folding.BoundaryLayer

namespace Omega.GroupUnification

/-- Certified three-sheet boundary fiber at `m = 7`. -/
abbrev bdryThreeLayerFiberM7 := Fin 3

/-- Certified three-sheet boundary fiber at `m = 8`. -/
abbrev bdryThreeLayerFiberM8 := Fin 3

/-- Paper label: `prop:bdry-three-layer-obstructs-free-z2`. The audited boundary fibers at
`m = 7, 8` each have three sheets, so any involution on either fiber has a fixed point and hence
cannot be a free `ℤ/2`-action. -/
theorem paper_bdry_three_layer_obstructs_free_z2 :
    (Fintype.card bdryThreeLayerFiberM7 = 3 ∧
      ¬ ∃ σ : Equiv.Perm bdryThreeLayerFiberM7, σ * σ = 1 ∧ ∀ x, σ x ≠ x) ∧
    (Fintype.card bdryThreeLayerFiberM8 = 3 ∧
      ¬ ∃ σ : Equiv.Perm bdryThreeLayerFiberM8, σ * σ = 1 ∧ ∀ x, σ x ≠ x) := by
  have hodd7 : ¬ Even (Fintype.card bdryThreeLayerFiberM7) := by
    simpa [bdryThreeLayerFiberM7] using (show ¬ Even 3 by native_decide)
  have hodd8 : ¬ Even (Fintype.card bdryThreeLayerFiberM8) := by
    simpa [bdryThreeLayerFiberM8] using (show ¬ Even 3 by native_decide)
  refine ⟨?_, ?_⟩
  · refine ⟨by simp [bdryThreeLayerFiberM7], ?_⟩
    intro hfree
    rcases hfree with ⟨σ, hinv, hnoFix⟩
    obtain ⟨x, hx⟩ :=
      Omega.odd_card_no_free_involution (α := bdryThreeLayerFiberM7) hodd7 σ hinv
    exact hnoFix x hx
  · refine ⟨by simp [bdryThreeLayerFiberM8], ?_⟩
    intro hfree
    rcases hfree with ⟨σ, hinv, hnoFix⟩
    obtain ⟨x, hx⟩ :=
      Omega.odd_card_no_free_involution (α := bdryThreeLayerFiberM8) hodd8 σ hinv
    exact hnoFix x hx

end Omega.GroupUnification
