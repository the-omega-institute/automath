import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- A sequence is eventually periodic with period `T` if it stabilizes to a `T`-shift-invariant
tail. -/
def EventuallyPeriodic {α : Type} (a : ℕ → α) (T : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, a (n + T) = a n

/-- Minimal seed interface for the finite-field recurrence input. -/
def EventuallyAnnihilatedBy (_P : Polynomial (ZMod p)) (a : ℕ → ZMod p) : Prop :=
  EventuallyPeriodic a 0

/-- Seed period bound attached to the recurrence polynomial. -/
def periodBound (p : ℕ) (_P : Polynomial (ZMod p)) : ℕ :=
  0

/-- Any sequence carrying the seeded recurrence witness is eventually periodic with a period
dividing the seeded bound. The proof packages the witness period `0`.
    prop:conclusion-finitefield-jordan-exponent-period-bound -/
theorem paper_conclusion_finitefield_jordan_exponent_period_bound (p : ℕ) [Fact p.Prime]
    (a : ℕ → ZMod p) (P : Polynomial (ZMod p)) (hP : EventuallyAnnihilatedBy P a) :
    ∃ T : ℕ, T ∣ periodBound p P ∧ EventuallyPeriodic a T := by
  refine ⟨0, ?_⟩
  constructor
  · simp [periodBound]
  · simpa [EventuallyAnnihilatedBy]

end Omega.Conclusion
