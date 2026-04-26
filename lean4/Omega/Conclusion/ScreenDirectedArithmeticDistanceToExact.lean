import Omega.Conclusion.ScreenMinimalExactExtensionContractionBasis

namespace Omega.Conclusion

open Finset

/-- Paper label: `thm:conclusion-screen-directed-arithmetic-distance-to-exact`. -/
theorem paper_conclusion_screen_directed_arithmetic_distance_to_exact
    (D : ScreenDeficitData) (S : Finset D.Edge) :
    (∃ T : Finset D.Edge, D.MinimalExactExtension S T ∧ (T \ S).card = D.deficit S) ∧
      ∀ T : Finset D.Edge, D.ExactExtension T → S ⊆ T →
        D.deficit S ≤ (T \ S).card ∧
          ((T \ S).card = D.deficit S → D.MinimalExactExtension S T) := by
  classical
  let B : Finset D.Edge := D.basis \ S
  have hB : D.ContractionBasisChoice S B := by
    refine ⟨by intro e he; simpa [B] using he, ?_⟩
    simp [B, ScreenDeficitData.deficit]
  let hEquiv := screenMinimalExactExtensionContractionBasisEquiv D S
  let T0 : {T : Finset D.Edge // D.MinimalExactExtension S T} := hEquiv.symm ⟨B, hB⟩
  refine ⟨?_, ?_⟩
  · exact ⟨T0.1, T0.2, T0.2.2.2⟩
  · intro T hExact hST
    have hzero : (D.basis \ T).card = 0 := by
      simpa [ScreenDeficitData.ExactExtension, ScreenDeficitData.deficit] using hExact
    have hbasis : D.basis ⊆ T := by
      exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hzero)
    have hmissing : D.basis \ S ⊆ T \ S := by
      intro e he
      simp only [mem_sdiff] at he ⊢
      exact ⟨hbasis he.1, he.2⟩
    refine ⟨?_, ?_⟩
    · simpa [ScreenDeficitData.deficit] using Finset.card_le_card hmissing
    · intro hcard
      exact ⟨hST, hExact, hcard⟩

end Omega.Conclusion
