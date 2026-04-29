import Mathlib.Tactic

namespace Omega.Conclusion

/-- Window-`6` reversible capacity curve from the three multiplicity classes.
    thm:conclusion-window6-exact-reversible-capacity-curve -/
theorem paper_conclusion_window6_exact_reversible_capacity_curve (B : ℕ) :
    (let C6 := 8 * min 2 (2 ^ B) + 4 * min 3 (2 ^ B) + 9 * min 4 (2 ^ B);
      (B = 0 → C6 = 21) ∧ (B = 1 → C6 = 42) ∧ (2 ≤ B → C6 = 64)) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro hB
    subst B
    norm_num
  · intro hB
    subst B
    norm_num
  · intro hB
    have h4 : 4 ≤ 2 ^ B := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB
    have h2 : 2 ≤ 2 ^ B := by omega
    have h3 : 3 ≤ 2 ^ B := by
      omega
    rw [Nat.min_eq_left h2, Nat.min_eq_left h3, Nat.min_eq_left h4]

end Omega.Conclusion
