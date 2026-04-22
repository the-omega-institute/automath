import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The essential prime axis is exactly the union of denominator-degeneration and
discriminant-collision primes. -/
def essentialPrimeAxis (badDenominator badDiscriminant : Finset ℕ) : Finset ℕ :=
  badDenominator ∪ badDiscriminant

/-- Good primes are the unramified primes outside both exceptional finite sets. -/
def goodPrimeOnAxis (p : ℕ) (badDenominator badDiscriminant : Finset ℕ) : Prop :=
  Nat.Prime p ∧ p ∉ badDenominator ∧ p ∉ badDiscriminant

/-- Bad primes are precisely the primes where either denominator degeneration or discriminant
collision occurs. -/
def badPrimeOnAxis (p : ℕ) (badDenominator badDiscriminant : Finset ℕ) : Prop :=
  Nat.Prime p ∧ (p ∈ badDenominator ∨ p ∈ badDiscriminant)

/-- A finite label family is Hensel-stable when it is nonempty, contains the current prime label,
and the prime is good. -/
def henselStableLabels (p : ℕ) (badDenominator badDiscriminant labels : Finset ℕ) : Prop :=
  labels.Nonempty ∧ p ∈ labels ∧ goodPrimeOnAxis p badDenominator badDiscriminant

/-- Paper label: `thm:conclusion-essential-prime-axis-minimality`. Good primes admit a finite
singleton stable label on the unramified fiber, bad primes admit none, and therefore a prime can
be stably externalized by a finite label family exactly when it lies off the essential prime axis.
-/
theorem paper_conclusion_essential_prime_axis_minimality
    (badDenominator badDiscriminant : Finset ℕ) :
    (∀ {p : ℕ}, goodPrimeOnAxis p badDenominator badDiscriminant →
      ∃ labels : Finset ℕ, labels.card ≤ 1 ∧
        henselStableLabels p badDenominator badDiscriminant labels) ∧
    (∀ {p : ℕ}, badPrimeOnAxis p badDenominator badDiscriminant →
      ∀ labels : Finset ℕ, ¬ henselStableLabels p badDenominator badDiscriminant labels) ∧
    (∀ {p : ℕ}, Nat.Prime p →
      ((∃ labels : Finset ℕ, henselStableLabels p badDenominator badDiscriminant labels) ↔
        p ∉ essentialPrimeAxis badDenominator badDiscriminant)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    refine ⟨{p}, by simp [henselStableLabels, hp]⟩
  · intro p hpbad labels hlabels
    rcases hpbad with ⟨_, hbad⟩
    rcases hlabels.2.2 with ⟨_, hpden, hpdisc⟩
    cases hbad with
    | inl h =>
        exact hpden h
    | inr h =>
        exact hpdisc h
  · intro p hp
    constructor
    · rintro ⟨labels, hlabels⟩
      rcases hlabels.2.2 with ⟨_, hpden, hpdisc⟩
      simp [essentialPrimeAxis, hpden, hpdisc]
    · intro hpaxis
      have hgood : goodPrimeOnAxis p badDenominator badDiscriminant := by
        have hmem : p ∉ badDenominator ∧ p ∉ badDiscriminant := by
          simpa [essentialPrimeAxis, not_or] using hpaxis
        exact ⟨hp, hmem.1, hmem.2⟩
      exact ⟨{p}, by simp [henselStableLabels, hgood]⟩

end Omega.Conclusion
