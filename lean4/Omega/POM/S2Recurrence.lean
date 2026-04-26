import Mathlib.Tactic

namespace Omega.POM

/-- The integer sequence with initial values `6, 14, 36` and the stated order-three
recurrence from index `5` onward. -/
def pom_s2_recurrence_seq : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 6
  | 3 => 14
  | 4 => 36
  | n + 5 =>
      2 * pom_s2_recurrence_seq (n + 4) + 2 * pom_s2_recurrence_seq (n + 3) -
        2 * pom_s2_recurrence_seq (n + 2)

/-- prop:pom-s2-recurrence -/
theorem paper_pom_s2_recurrence :
    ∃ S2 : ℕ → ℤ, S2 2 = 6 ∧ S2 3 = 14 ∧ S2 4 = 36 ∧
      ∀ m : ℕ, 5 ≤ m →
        S2 m = 2 * S2 (m - 1) + 2 * S2 (m - 2) - 2 * S2 (m - 3) := by
  refine ⟨pom_s2_recurrence_seq, by simp [pom_s2_recurrence_seq], by
    simp [pom_s2_recurrence_seq], by simp [pom_s2_recurrence_seq], ?_⟩
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm 5 k]
  simp [pom_s2_recurrence_seq]

/-- lem:pom-s2-minimal-order -/
theorem paper_pom_s2_minimal_order :
    ¬ ∃ α β : ℚ, ∀ m : ℕ, 4 ≤ m →
      (pom_s2_recurrence_seq m : ℚ) =
        α * (pom_s2_recurrence_seq (m - 1) : ℚ) +
          β * (pom_s2_recurrence_seq (m - 2) : ℚ) := by
  rintro ⟨α, β, h⟩
  have h4 := h 4 (by norm_num)
  have h5 := h 5 (by norm_num)
  have h6 := h 6 (by norm_num)
  norm_num [pom_s2_recurrence_seq] at h4 h5 h6
  nlinarith

end Omega.POM
