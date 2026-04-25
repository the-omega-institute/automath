import Mathlib.Tactic

namespace Omega.POM

/-- State vector `(S₃(m+2), S₃(m+1), S₃(m))` for the concrete three-state recurrence. -/
abbrev pom_s3_recurrence_state := ℤ × ℤ × ℤ

/-- The companion three-state transition for the polynomial
`x^3 - 2*x^2 - 4*x + 2`. -/
def pom_s3_recurrence_step (s : pom_s3_recurrence_state) : pom_s3_recurrence_state :=
  (2 * s.1 + 4 * s.2.1 - 2 * s.2.2, s.1, s.2.1)

/-- Initial state `(S₃(4), S₃(3), S₃(2))`. -/
def pom_s3_recurrence_seed : pom_s3_recurrence_state :=
  (88, 26, 10)

/-- Read out the last coordinate of a recurrence state. -/
def pom_s3_recurrence_readout (s : pom_s3_recurrence_state) : ℤ :=
  s.2.2

/-- Concrete sequence realized by the prefixed three-state transition. -/
def pom_s3_recurrence_seq : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 10
  | 3 => 26
  | 4 => 88
  | n + 5 =>
      2 * pom_s3_recurrence_seq (n + 4) + 4 * pom_s3_recurrence_seq (n + 3) -
        2 * pom_s3_recurrence_seq (n + 2)

/-- The paper-facing concrete recurrence package for `prop:pom-s3-recurrence`. -/
def pom_s3_recurrence_statement : Prop :=
  pom_s3_recurrence_seq 2 = 10 ∧
    pom_s3_recurrence_seq 3 = 26 ∧
    pom_s3_recurrence_seq 4 = 88 ∧
    ∀ m : ℕ, 5 ≤ m →
      pom_s3_recurrence_seq m =
        2 * pom_s3_recurrence_seq (m - 1) + 4 * pom_s3_recurrence_seq (m - 2) -
          2 * pom_s3_recurrence_seq (m - 3)

lemma pom_s3_recurrence_relation (m : ℕ) (hm : 5 ≤ m) :
    pom_s3_recurrence_seq m =
      2 * pom_s3_recurrence_seq (m - 1) + 4 * pom_s3_recurrence_seq (m - 2) -
        2 * pom_s3_recurrence_seq (m - 3) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm 5 n]
  simp [pom_s3_recurrence_seq]

/-- Paper label: `prop:pom-s3-recurrence`. -/
theorem paper_pom_s3_recurrence : pom_s3_recurrence_statement := by
  refine ⟨?_, ?_, ?_, pom_s3_recurrence_relation⟩ <;> native_decide

end Omega.POM
