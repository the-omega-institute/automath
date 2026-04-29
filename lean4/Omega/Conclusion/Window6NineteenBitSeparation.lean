import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-window6-19bit-separation`. -/
theorem paper_conclusion_window6_19bit_separation :
    (let C6 : ℕ → ℕ :=
      fun B => 8 * min 2 (2 ^ B) + 4 * min 3 (2 ^ B) + 9 * min 4 (2 ^ B)
    C6 0 = 21 ∧ C6 1 = 42 ∧ (∀ B : ℕ, 2 ≤ B → C6 B = 64) ∧
      (∀ B : ℕ, C6 B = 64 → 2 ≤ B) ∧ 21 - 2 = 19) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · intro B hB
    have hpow : 4 ≤ 2 ^ B := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ B := by exact Nat.pow_le_pow_right (by norm_num) hB
    have h2 : min 2 (2 ^ B) = 2 := by
      exact min_eq_left (le_trans (by norm_num : 2 ≤ 4) hpow)
    have h3 : min 3 (2 ^ B) = 3 := by
      exact min_eq_left (le_trans (by norm_num : 3 ≤ 4) hpow)
    have h4 : min 4 (2 ^ B) = 4 := by
      exact min_eq_left hpow
    simp [h2, h3, h4]
  · intro B hB64
    by_contra hlt
    have hBlt : B < 2 := by omega
    interval_cases B <;> norm_num at hB64
  · norm_num

end Omega.Conclusion
