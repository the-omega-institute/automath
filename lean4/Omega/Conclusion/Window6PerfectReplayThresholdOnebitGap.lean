import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-perfect-replay-threshold-onebit-gap`. -/
theorem paper_conclusion_window6_perfect_replay_threshold_onebit_gap
    (d : Fin 21 → ℕ)
    (h2 : (Finset.univ.filter (fun x : Fin 21 => d x = 2)).card = 8)
    (h3 : (Finset.univ.filter (fun x : Fin 21 => d x = 3)).card = 4)
    (h4 : (Finset.univ.filter (fun x : Fin 21 => d x = 4)).card = 9)
    (hrange : ∀ x, d x = 2 ∨ d x = 3 ∨ d x = 4) :
    (∀ x, d x ≤ 4) ∧ (∃ x, d x = 4) ∧
      (∑ x : Fin 21, Nat.min (d x) 2) = 42 ∧ (42 : ℚ) / 64 = 21 / 32 := by
  have _ : (Finset.univ.filter (fun x : Fin 21 => d x = 2)).card = 8 := h2
  have _ : (Finset.univ.filter (fun x : Fin 21 => d x = 3)).card = 4 := h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rcases hrange x with h | h | h <;> omega
  · have hpos : 0 < (Finset.univ.filter (fun x : Fin 21 => d x = 4)).card := by
      rw [h4]
      norm_num
    rcases Finset.card_pos.mp hpos with ⟨x, hx⟩
    exact ⟨x, (Finset.mem_filter.mp hx).2⟩
  · calc
      (∑ x : Fin 21, Nat.min (d x) 2) = ∑ _x : Fin 21, 2 := by
        apply Finset.sum_congr rfl
        intro x _hx
        rcases hrange x with h | h | h <;> simp [h]
      _ = 42 := by norm_num
  · norm_num

end Omega.Conclusion
