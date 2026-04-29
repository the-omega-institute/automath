import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset

/-- Concrete finite screen datum for a corank-style deficit audit. The distinguished finite set
`basis` plays the role of a contraction basis whose missing elements are inserted one-by-one. -/
structure ScreenDeficitData where
  Edge : Type
  decEqEdge : DecidableEq Edge
  basis : Finset Edge

attribute [instance] ScreenDeficitData.decEqEdge

/-- The residual deficit is the number of basis elements still missing from the partial screen. -/
def ScreenDeficitData.deficit (D : ScreenDeficitData) (S : Finset D.Edge) : ℕ :=
  (D.basis \ S).card

/-- The `j`-th prefix screen obtained by adjoining the first `j` missing basis elements. -/
noncomputable def ScreenDeficitData.prefix (D : ScreenDeficitData) (S : Finset D.Edge) (j : ℕ) :
    Finset D.Edge :=
  S ∪ ((D.basis \ S).toList.take j).toFinset

/-- The residual deficit after inserting the first `j` basis elements. -/
noncomputable def ScreenDeficitData.prefixDeficit
    (D : ScreenDeficitData) (S : Finset D.Edge) (j : ℕ) : ℕ :=
  ((D.basis \ S).toList.drop j).toFinset.card

/-- The paper-facing unit descent chain package: each prefix contains exactly `j` inserted basis
elements, and the remaining deficit drops from the initial gap by exactly `j`, hence by one at
every step. -/
def ScreenDeficitUnitDescentChain (D : ScreenDeficitData) (S : Finset D.Edge) : Prop :=
  let L := (D.basis \ S).toList
  (∀ j, j ≤ L.length →
      ((L.take j).toFinset.card = j ∧ D.prefixDeficit S j = D.deficit S - j)) ∧
    (∀ j, j < L.length → D.prefixDeficit S (j + 1) + 1 = D.prefixDeficit S j) ∧
    D.prefixDeficit S L.length = 0

/-- Paper label: `thm:conclusion-screen-deficit-unit-descent-chain`. -/
theorem paper_conclusion_screen_deficit_unit_descent_chain
    (D : ScreenDeficitData) (S : Finset D.Edge) : ScreenDeficitUnitDescentChain D S := by
  classical
  let L : List D.Edge := (D.basis \ S).toList
  have hnodup : L.Nodup := by
    simpa [L] using (D.basis \ S).nodup_toList
  have hdeficit : D.deficit S = L.length := by
    calc
      D.deficit S = (D.basis \ S).card := rfl
      _ = ((D.basis \ S).toList).toFinset.card := by simp
      _ = ((D.basis \ S).toList).length := by
        simpa using List.toFinset_card_of_nodup ((D.basis \ S).nodup_toList)
      _ = L.length := by simp [L]
  have htake_card :
      ∀ j, j ≤ L.length → (L.take j).toFinset.card = j := by
    intro j hj
    calc
      (L.take j).toFinset.card = (L.take j).length := by
        simpa using List.toFinset_card_of_nodup (hnodup.sublist (List.take_sublist j L))
      _ = j := by simp [List.length_take, hj]
  have hdrop_card :
      ∀ j, D.prefixDeficit S j = L.length - j := by
    intro j
    calc
      D.prefixDeficit S j = (((D.basis \ S).toList.drop j).toFinset.card) := rfl
      _ = ((D.basis \ S).toList.drop j).length := by
        simpa using
          List.toFinset_card_of_nodup ((D.basis \ S).nodup_toList.sublist (List.drop_sublist j _))
      _ = ((D.basis \ S).toList).length - j := by simp
      _ = L.length - j := by simp [L]
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    refine ⟨htake_card j hj, ?_⟩
    rw [hdrop_card, hdeficit]
  · intro j hj
    rw [hdrop_card, hdrop_card]
    have hstep : L.length - (j + 1) + 1 = L.length - j := by
      have hj' : j + 1 ≤ L.length := Nat.succ_le_of_lt hj
      omega
    simpa [hstep]
  · rw [hdrop_card]
    simp [L]

end Omega.Conclusion
