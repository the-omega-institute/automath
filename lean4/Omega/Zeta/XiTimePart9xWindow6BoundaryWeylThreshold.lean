import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9x-window6-boundary-weyl-threshold`. -/
theorem paper_xi_time_part9x_window6_boundary_weyl_threshold {α : Type*} [DecidableEq α]
    (Y boundary cyclic : Finset α) (hdisj : Disjoint boundary cyclic) (hbd : boundary.card = 3)
    (hsubBd : boundary ⊆ Y) (hsub : Y ⊆ boundary ∪ cyclic)
    (horbit : (Y ∩ cyclic).card ∈ ({0, 6, 12, 18} : Finset ℕ)) :
    Y.card ∈ ({3, 9, 15, 21} : Finset ℕ) ∧
      ((Y ∩ cyclic).Nonempty → 9 ≤ Y.card) := by
  let C := Y ∩ cyclic
  have hYC : Y = boundary ∪ C := by
    ext x
    constructor
    · intro hx
      have hx' := hsub hx
      simp only [Finset.mem_union] at hx'
      rcases hx' with hxbd | hxcyc
      · simpa only [Finset.mem_union] using (Or.inl hxbd : x ∈ boundary ∨ x ∈ C)
      · have hxC : x ∈ C := by simp [C, hx, hxcyc]
        simpa only [Finset.mem_union] using (Or.inr hxC : x ∈ boundary ∨ x ∈ C)
    · intro hx
      simp only [Finset.mem_union] at hx
      rcases hx with hxbd | hxC
      · exact hsubBd hxbd
      · have hxCY : x ∈ Y ∧ x ∈ cyclic := by simpa [C] using hxC
        exact hxCY.1
  have hdisjC : Disjoint boundary C := hdisj.mono_right (by
    intro x hx
    have hxCY : x ∈ Y ∧ x ∈ cyclic := by simpa [C] using hx
    exact hxCY.2)
  have hcard : Y.card = 3 + C.card := by
    calc
      Y.card = (boundary ∪ C).card := by rw [hYC]
      _ = boundary.card + C.card := Finset.card_union_of_disjoint hdisjC
      _ = 3 + C.card := by rw [hbd]
  have hCmem : C.card ∈ ({0, 6, 12, 18} : Finset ℕ) := by
    simpa [C] using horbit
  have hCcases : C.card = 0 ∨ C.card = 6 ∨ C.card = 12 ∨ C.card = 18 := by
    simpa using hCmem
  constructor
  · rw [hcard]
    rcases hCcases with h0 | h6 | h12 | h18
    · simp [h0]
    · simp [h6]
    · simp [h12]
    · simp [h18]
  · intro hnonempty
    rw [hcard]
    have hCpos : 0 < C.card := Finset.card_pos.mpr hnonempty
    rcases hCcases with h0 | h6 | h12 | h18 <;> omega

end Omega.Zeta
