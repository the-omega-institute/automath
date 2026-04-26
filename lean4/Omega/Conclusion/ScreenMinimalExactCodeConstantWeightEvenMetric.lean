import Mathlib.Algebra.Ring.Parity
import Omega.Conclusion.ScreenBasisExchangeGraphGeodesicRigidity

namespace Omega.Conclusion

open Finset

/-- Paper label: `cor:conclusion-screen-minimal-exact-code-constant-weight-even-metric`. -/
theorem paper_conclusion_screen_minimal_exact_code_constant_weight_even_metric
    (D : ScreenBasisExchangeData) :
    (∀ {B : Finset D.Edge}, D.IsBasis B → B.card = D.basisSize) ∧
      (∀ {B B' : Finset D.Edge}, D.IsBasis B → D.IsBasis B' →
        Even (D.arithmeticDistance B B')) ∧
      ((∃ B B' : Finset D.Edge, D.IsBasis B ∧ D.IsBasis B' ∧ B ≠ B') →
        ∃ B B' : Finset D.Edge,
          D.IsBasis B ∧ D.IsBasis B' ∧ D.arithmeticDistance B B' = 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    exact hB
  · intro B B' hB hB'
    have hcard : B.card = B'.card := by
      calc
        B.card = D.basisSize := hB
        _ = B'.card := hB'.symm
    have hsdiff : (B \ B').card = (B' \ B).card := Finset.card_sdiff_comm hcard
    refine ⟨(B \ B').card, ?_⟩
    unfold ScreenBasisExchangeData.arithmeticDistance
    omega
  · intro hExists
    rcases hExists with ⟨B, B', hB, hB', hneq⟩
    have hcard : B.card = B'.card := by
      calc
        B.card = D.basisSize := hB
        _ = B'.card := hB'.symm
    have hx : ∃ x, x ∈ B ∧ x ∉ B' := by
      by_contra hnot
      have hsubset : B ⊆ B' := by
        intro x hxB
        by_contra hxB'
        exact hnot ⟨x, hxB, hxB'⟩
      have hEq : B = B' := Finset.eq_of_subset_of_card_le hsubset (by omega)
      exact hneq hEq
    have hy : ∃ y, y ∈ B' ∧ y ∉ B := by
      by_contra hnot
      have hsubset : B' ⊆ B := by
        intro y hyB'
        by_contra hyB
        exact hnot ⟨y, hyB', hyB⟩
      have hEq : B' = B := Finset.eq_of_subset_of_card_le hsubset (by omega)
      exact hneq hEq.symm
    rcases hx with ⟨x, hxB, hxB'⟩
    rcases hy with ⟨y, hyB', hyB⟩
    have hxy : x ≠ y := by
      intro h
      exact hyB (h ▸ hxB)
    let C : Finset D.Edge := insert y (erase B x)
    have hC : D.IsBasis C := by
      unfold C ScreenBasisExchangeData.IsBasis
      have hyErase : y ∉ erase B x := by
        intro hyErase
        exact hyB (Finset.mem_of_mem_erase hyErase)
      have hcard_pos : 1 ≤ B.card := Finset.one_le_card.mpr ⟨x, hxB⟩
      calc
        #(insert y (erase B x)) = #(erase B x) + 1 := Finset.card_insert_of_notMem hyErase
        _ = B.card := by rw [Finset.card_erase_of_mem hxB, Nat.sub_add_cancel hcard_pos]
        _ = D.basisSize := hB
    have hsdiff_left : B \ C = ({x} : Finset D.Edge) := by
      ext e
      by_cases he : e = x
      · subst he
        simp [C, hxB, hxy]
      · constructor
        · intro hmem
          simp only [mem_sdiff] at hmem
          have hInErase : e ∈ erase B x := Finset.mem_erase.mpr ⟨he, hmem.1⟩
          exact False.elim (hmem.2 (by simp [C, hInErase]))
        · intro hmem
          simp [he] at hmem
    have hsdiff_right : C \ B = ({y} : Finset D.Edge) := by
      ext e
      by_cases he : e = y
      · subst he
        simp [C, hyB]
      · constructor
        · intro hmem
          simp only [mem_sdiff] at hmem
          have hInErase : e ∈ erase B x := by
            simpa [C, he] using hmem.1
          exact False.elim (hmem.2 (Finset.mem_erase.mp hInErase).2)
        · intro hmem
          simp [he] at hmem
    refine ⟨B, C, hB, hC, ?_⟩
    calc
      D.arithmeticDistance B C = (B \ C).card + (C \ B).card := by
        rfl
      _ = ({x} : Finset D.Edge).card + ({y} : Finset D.Edge).card := by
        rw [hsdiff_left, hsdiff_right]
      _ = 2 := by simp

end Omega.Conclusion
