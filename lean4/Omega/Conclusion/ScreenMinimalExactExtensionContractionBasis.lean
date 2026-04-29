import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic
import Omega.Conclusion.ScreenDeficitUnitDescentChain

namespace Omega.Conclusion

open Finset

/-- A screen extension is exact when it has no remaining deficit. -/
def ScreenDeficitData.ExactExtension (D : ScreenDeficitData) (T : Finset D.Edge) : Prop :=
  D.deficit T = 0

/-- A minimal exact extension of `S` is an exact extension that adds exactly the missing deficit. -/
def ScreenDeficitData.MinimalExactExtension
    (D : ScreenDeficitData) (S T : Finset D.Edge) : Prop :=
  S ⊆ T ∧ D.ExactExtension T ∧ (T \ S).card = D.deficit S

/-- In the deficit model, a contraction-basis choice is a full-cardinality subset of the missing
basis elements. -/
def ScreenDeficitData.ContractionBasisChoice
    (D : ScreenDeficitData) (S B : Finset D.Edge) : Prop :=
  B ⊆ D.basis \ S ∧ B.card = D.deficit S

private lemma exactExtension_basis_subset
    (D : ScreenDeficitData) {T : Finset D.Edge} (hT : D.ExactExtension T) :
    D.basis ⊆ T := by
  have hzero : (D.basis \ T).card = 0 := by
    simpa [ScreenDeficitData.ExactExtension, ScreenDeficitData.deficit] using hT
  exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hzero)

private lemma minimalExactExtension_sdiff_eq_missing
    (D : ScreenDeficitData) {S T : Finset D.Edge}
    (hT : D.MinimalExactExtension S T) :
    T \ S = D.basis \ S := by
  rcases hT with ⟨hST, hExact, hcard⟩
  have hbasis : D.basis ⊆ T := exactExtension_basis_subset D hExact
  have hsubset : D.basis \ S ⊆ T \ S := by
    intro e he
    simp only [mem_sdiff] at he ⊢
    exact ⟨hbasis he.1, he.2⟩
  have hcard_le : (T \ S).card ≤ (D.basis \ S).card := by
    simpa [ScreenDeficitData.deficit] using Nat.le_of_eq hcard
  exact (Finset.eq_of_subset_of_card_le hsubset hcard_le).symm

private lemma contractionBasisChoice_eq_missing
    (D : ScreenDeficitData) {S B : Finset D.Edge}
    (hB : D.ContractionBasisChoice S B) :
    B = D.basis \ S := by
  rcases hB with ⟨hsub, hcard⟩
  have hcard_le : (D.basis \ S).card ≤ B.card := by
    simpa [ScreenDeficitData.deficit] using Nat.le_of_eq hcard.symm
  exact Finset.eq_of_subset_of_card_le hsub hcard_le

private lemma union_sdiff_eq_of_subset {α : Type*} [DecidableEq α] {S T : Finset α}
    (hST : S ⊆ T) : S ∪ (T \ S) = T := by
  ext e
  by_cases heS : e ∈ S
  · simp [heS, hST heS]
  · simp [heS]

private lemma sdiff_union_eq_of_disjoint_subset {α : Type*} [DecidableEq α] {S B : Finset α}
    (hBS : Disjoint B S) : (S ∪ B) \ S = B := by
  ext e
  constructor
  · intro he
    simp only [mem_sdiff, mem_union] at he
    exact he.1.resolve_left he.2
  · intro heB
    have heS : e ∉ S := by
      intro hS
      exact (Finset.disjoint_left.mp hBS heB hS)
    simp [heB, heS]

/-- The forward/backward map between minimal exact extensions and contraction-basis choices. -/
noncomputable def screenMinimalExactExtensionContractionBasisEquiv
    (D : ScreenDeficitData) (S : Finset D.Edge) :
    {T : Finset D.Edge // D.MinimalExactExtension S T} ≃
      {B : Finset D.Edge // D.ContractionBasisChoice S B} where
  toFun T := by
    refine ⟨T.1 \ S, ?_⟩
    have hEq : T.1 \ S = D.basis \ S := minimalExactExtension_sdiff_eq_missing D T.2
    refine ⟨?_, ?_⟩
    · simpa [hEq]
    · simpa [hEq, ScreenDeficitData.deficit]
  invFun B := by
    refine ⟨S ∪ B.1, ?_⟩
    rcases B.2 with ⟨hsub, hcard⟩
    have hEq : B.1 = D.basis \ S := contractionBasisChoice_eq_missing D B.2
    have hbasis : D.basis ⊆ S ∪ B.1 := by
      intro e he
      by_cases heS : e ∈ S
      · simp [heS]
      · have heB : e ∈ B.1 := by
          rw [hEq]
          simp [he, heS]
        simp [heS, heB]
    have hdisj : Disjoint B.1 S := by
      refine Finset.disjoint_left.mpr ?_
      intro e heB heS
      have : e ∈ D.basis \ S := hsub heB
      simpa [mem_sdiff, heS] using this
    refine ⟨by simp, ?_, ?_⟩
    · unfold ScreenDeficitData.ExactExtension ScreenDeficitData.deficit
      exact Finset.card_eq_zero.mpr (Finset.sdiff_eq_empty_iff_subset.mpr hbasis)
    · rw [sdiff_union_eq_of_disjoint_subset hdisj, hcard]
  left_inv T := by
    apply Subtype.ext
    exact union_sdiff_eq_of_subset T.2.1
  right_inv B := by
    apply Subtype.ext
    rcases B.2 with ⟨hsub, _hcard⟩
    have hdisj : Disjoint B.1 S := by
      refine Finset.disjoint_left.mpr ?_
      intro e heB heS
      have : e ∈ D.basis \ S := hsub heB
      simpa [mem_sdiff, heS] using this
    exact sdiff_union_eq_of_disjoint_subset hdisj

/-- Paper label: `thm:conclusion-screen-minimal-exact-extension-contraction-basis`. -/
theorem paper_conclusion_screen_minimal_exact_extension_contraction_basis
    (D : ScreenDeficitData) (S : Finset D.Edge) :
    (∀ T : Finset D.Edge,
      D.MinimalExactExtension S T ↔
        ∃ B : Finset D.Edge, D.ContractionBasisChoice S B ∧ T = S ∪ B) ∧
      Nonempty ({T : Finset D.Edge // D.MinimalExactExtension S T} ≃
        {B : Finset D.Edge // D.ContractionBasisChoice S B}) := by
  refine ⟨?_, ⟨screenMinimalExactExtensionContractionBasisEquiv D S⟩⟩
  intro T
  constructor
  · intro hT
    refine ⟨T \ S, ?_, ?_⟩
    · have hEq : T \ S = D.basis \ S := minimalExactExtension_sdiff_eq_missing D hT
      refine ⟨?_, ?_⟩
      · simpa [hEq]
      · simpa [hEq, ScreenDeficitData.deficit]
    · exact (union_sdiff_eq_of_subset hT.1).symm
  · rintro ⟨B, hB, rfl⟩
    rcases hB with ⟨hsub, hcard⟩
    have hbasis : D.basis ⊆ S ∪ B := by
      intro e he
      by_cases heS : e ∈ S
      · simp [heS]
      · have heB : e ∈ B := by
          have : e ∈ D.basis \ S := by simp [he, heS]
          exact by
            have hEq : B = D.basis \ S := contractionBasisChoice_eq_missing D ⟨hsub, hcard⟩
            simpa [hEq] using this
        simp [heS, heB]
    have hdisj : Disjoint B S := by
      refine Finset.disjoint_left.mpr ?_
      intro e heB heS
      have : e ∈ D.basis \ S := hsub heB
      simpa [mem_sdiff, heS] using this
    refine ⟨by simp, ?_, ?_⟩
    · unfold ScreenDeficitData.ExactExtension ScreenDeficitData.deficit
      exact Finset.card_eq_zero.mpr (Finset.sdiff_eq_empty_iff_subset.mpr hbasis)
    · simpa [sdiff_union_eq_of_disjoint_subset hdisj] using hcard

end Omega.Conclusion
