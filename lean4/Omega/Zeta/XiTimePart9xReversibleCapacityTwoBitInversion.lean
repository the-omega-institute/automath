namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9x-reversible-capacity-two-bit-inversion`. -/
theorem paper_xi_time_part9x_reversible_capacity_two_bit_inversion :
    (let C6 : Nat -> Nat := fun B =>
      8 * min 2 (2 ^ B) + 4 * min 3 (2 ^ B) + 9 * min 4 (2 ^ B)
    C6 0 = 21 ∧ C6 1 = 42 ∧
      (∀ B : Nat, 2 ≤ B -> C6 B = 64) ∧
      (∀ B : Nat, C6 B = 64 -> 2 ≤ B)) := by
  dsimp
  refine ⟨by native_decide, by native_decide, ?_, ?_⟩
  · intro B hB
    have h4 : 4 ≤ 2 ^ B := by
      calc
        4 = 2 ^ 2 := by native_decide
        _ ≤ 2 ^ B := Nat.pow_le_pow_right (by decide : 0 < 2) hB
    have h3 : 3 ≤ 2 ^ B := Nat.le_trans (by decide : 3 ≤ 4) h4
    have h2 : 2 ≤ 2 ^ B := Nat.le_trans (by decide : 2 ≤ 4) h4
    rw [Nat.min_eq_left h2, Nat.min_eq_left h3, Nat.min_eq_left h4]
  · intro B hC
    cases B with
    | zero =>
        exact False.elim ((by native_decide :
          ¬ (8 * min 2 (2 ^ 0) + 4 * min 3 (2 ^ 0) + 9 * min 4 (2 ^ 0) = 64)) hC)
    | succ B =>
        cases B with
        | zero =>
            exact False.elim ((by native_decide :
              ¬ (8 * min 2 (2 ^ 1) + 4 * min 3 (2 ^ 1) + 9 * min 4 (2 ^ 1) = 64)) hC)
        | succ B =>
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le B))

end Omega.Zeta
