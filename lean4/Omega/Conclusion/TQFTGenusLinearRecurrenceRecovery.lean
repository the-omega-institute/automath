import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

section TQFTGenusLinearRecurrenceRecovery

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The genus sequence written as a finite exponential sum over the multiplicity values `d(x)`. -/
def conclusion_tqft_genus_linear_recurrence_recovery_genus_sequence (d : X → Nat) (g : ℕ) : ℤ :=
  ∑ x, (d x : ℤ) ^ g

/-- The finite prefix of genus values used as recovery data. -/
def conclusion_tqft_genus_linear_recurrence_recovery_prefix (d : X → Nat) :
    Fin (Fintype.card X + 1) → ℤ :=
  fun i => conclusion_tqft_genus_linear_recurrence_recovery_genus_sequence d i

/-- The canonical recovered sequence obtained by splicing the stored prefix with the closed
finite-exponential formula. -/
def conclusion_tqft_genus_linear_recurrence_recovery_recovered_sequence (d : X → Nat) : ℕ → ℤ :=
  fun g =>
    if h : g ≤ Fintype.card X then
      conclusion_tqft_genus_linear_recurrence_recovery_prefix d ⟨g, Nat.lt_succ_of_le h⟩
    else
      conclusion_tqft_genus_linear_recurrence_recovery_genus_sequence d g

/-- Chapter-local package: the genus values form a finite exponential sum, each mode satisfies its
order-`1` linear recurrence, the recorded prefix is exact, and the induced recovered sequence
coincides with the original genus tower. -/
def conclusion_tqft_genus_linear_recurrence_recovery_statement (d : X → Nat) : Prop :=
  (∀ g, conclusion_tqft_genus_linear_recurrence_recovery_genus_sequence d g = ∑ x, (d x : ℤ) ^ g) ∧
    (∀ x g, (d x : ℤ) ^ (g + 1) = (d x : ℤ) * (d x : ℤ) ^ g) ∧
    (∀ i : Fin (Fintype.card X + 1),
      conclusion_tqft_genus_linear_recurrence_recovery_prefix d i =
        conclusion_tqft_genus_linear_recurrence_recovery_genus_sequence d i) ∧
    conclusion_tqft_genus_linear_recurrence_recovery_recovered_sequence d =
      conclusion_tqft_genus_linear_recurrence_recovery_genus_sequence d

/-- Paper label: `prop:conclusion-tqft-genus-linear-recurrence-recovery`. The genus tower is a
finite exponential sum over the multiplicity spectrum, each exponential mode obeys its linear
recurrence, and the exact finite prefix recovers the same genus sequence. -/
theorem paper_conclusion_tqft_genus_linear_recurrence_recovery {X : Type} [Fintype X]
    [DecidableEq X] (d : X → Nat) :
    conclusion_tqft_genus_linear_recurrence_recovery_statement d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    rfl
  · intro x g
    rw [pow_succ, mul_comm]
  · intro i
    rfl
  · funext g
    by_cases h : g ≤ Fintype.card X
    · simp [conclusion_tqft_genus_linear_recurrence_recovery_recovered_sequence, h,
        conclusion_tqft_genus_linear_recurrence_recovery_prefix,
        conclusion_tqft_genus_linear_recurrence_recovery_genus_sequence]
    · simp [conclusion_tqft_genus_linear_recurrence_recovery_recovered_sequence, h]

end TQFTGenusLinearRecurrenceRecovery

end

end Omega.Conclusion
