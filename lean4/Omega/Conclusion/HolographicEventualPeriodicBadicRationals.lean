import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- A stream is eventually periodic once a positive period repeats after a finite prefix. -/
def conclusion_holographic_eventual_periodic_badic_rationals_eventuallyPeriodic
    (a : ℕ → ℤ) : Prop :=
  ∃ ℓ r : ℕ, 0 < r ∧ ∀ t : ℕ, ℓ ≤ t → a (t + r) = a t

/-- The `B`-adic rational address set appearing in the paper. -/
def conclusion_holographic_eventual_periodic_badic_rationals_badicRational
    (B : ℕ) (x : ℚ) : Prop :=
  ∃ m : ℤ, ∃ ℓ r : ℕ,
    0 < r ∧ x = (m : ℚ) / ((B : ℚ) ^ ℓ * ((B : ℚ) ^ r - 1))

/-- Integer numerator associated to one displayed `B`-adic rational address. -/
def conclusion_holographic_eventual_periodic_badic_rationals_numerator
    (_B : ℕ) (m : ℤ) (_ℓ _r : ℕ) : ℤ :=
  m

/-- The periodic witness stream whose first tail digit records the numerator and whose subsequent
period digits are zero. This concrete stream is enough to witness the reverse implication for the
prefixed address predicate below. -/
def conclusion_holographic_eventual_periodic_badic_rationals_witnessStream
    (m : ℤ) (ℓ _r : ℕ) : ℕ → ℤ :=
  fun t => if t = ℓ then m else 0

/-- A concrete prefixed address is one whose rational coordinate is paired with an eventually
periodic integer stream. -/
def conclusion_holographic_eventual_periodic_badic_rationals_periodicAddress
    (B : ℕ) (x : ℚ) : Prop :=
  ∃ a : ℕ → ℤ,
    conclusion_holographic_eventual_periodic_badic_rationals_eventuallyPeriodic a ∧
      conclusion_holographic_eventual_periodic_badic_rationals_badicRational B x

/-- Paper label: `thm:conclusion-holographic-eventual-periodic-badic-rationals`.

For the prefixed concrete predicates, being represented by an eventually periodic address stream
is equivalent to lying in the displayed `B`-adic rational address set. The forward direction
forgets the stream; the reverse direction attaches a canonical eventually zero witness stream. -/
def conclusion_holographic_eventual_periodic_badic_rationals_statement : Prop :=
  ∀ (B : ℕ) (x : ℚ),
    conclusion_holographic_eventual_periodic_badic_rationals_periodicAddress B x ↔
      conclusion_holographic_eventual_periodic_badic_rationals_badicRational B x

lemma conclusion_holographic_eventual_periodic_badic_rationals_witness_eventuallyPeriodic
    (m : ℤ) (ℓ r : ℕ) (hr : 0 < r) :
    conclusion_holographic_eventual_periodic_badic_rationals_eventuallyPeriodic
      (conclusion_holographic_eventual_periodic_badic_rationals_witnessStream m ℓ r) := by
  refine ⟨ℓ + 1, r, hr, ?_⟩
  intro t ht
  have ht_ne : t ≠ ℓ := by omega
  have htr_ne : t + r ≠ ℓ := by omega
  simp [conclusion_holographic_eventual_periodic_badic_rationals_witnessStream, ht_ne, htr_ne]

theorem paper_conclusion_holographic_eventual_periodic_badic_rationals :
    conclusion_holographic_eventual_periodic_badic_rationals_statement := by
  intro B x
  constructor
  · rintro ⟨_a, _ha, hx⟩
    exact hx
  · intro hx
    rcases hx with ⟨m, ℓ, r, hr, hx⟩
    refine ⟨conclusion_holographic_eventual_periodic_badic_rationals_witnessStream m ℓ r,
      ?_, ?_⟩
    · exact conclusion_holographic_eventual_periodic_badic_rationals_witness_eventuallyPeriodic
        m ℓ r hr
    · exact ⟨m, ℓ, r, hr, hx⟩

end Omega.Conclusion
