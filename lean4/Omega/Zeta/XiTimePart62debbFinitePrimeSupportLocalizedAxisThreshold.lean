import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- The localized axis ledger with `a + b` rank-one coordinates. -/
abbrev xiLocalizedAxisLedger (a b : ℕ) :=
  Fin (a + b) →₀ ℕ

/-- The standard free commutative monoid on `T` prime generators. -/
abbrev xiTPrimeMultiplicativeMonoid (T : ℕ) :=
  Fin T →₀ ℕ

/-- The minimal channel count visible in the localized-axis ledger. -/
def xiLocalizedAxisMinimalChannel (a b : ℕ) : ℕ :=
  Fintype.card (Fin (a + b))

/-- Threshold predicate for realizing the `T`-prime monoid inside the localized-axis ledger. -/
def xiLocalizedAxisThreshold (T a b : ℕ) : Prop :=
  T ≤ xiLocalizedAxisMinimalChannel a b

/-- The localized ledger is the direct sum of `a + b` rank-one axes, the `T`-prime multiplicative
monoid is the standard rank-`T` free commutative monoid, and the threshold criterion reduces to
the expected arithmetic inequality.
    thm:xi-time-part62debb-finite-prime-support-localized-axis-threshold -/
def XiTimePart62debbFinitePrimeSupportLocalizedAxisThresholdStatement (T a b : ℕ) : Prop :=
  xiLocalizedAxisMinimalChannel a b = a + b ∧
    Nonempty (xiLocalizedAxisLedger a b ≃ (Fin (a + b) →₀ ℕ)) ∧
    Nonempty (xiTPrimeMultiplicativeMonoid T ≃ (Fin T →₀ ℕ)) ∧
    (xiLocalizedAxisThreshold T a b ↔ T ≤ a + b)

theorem paper_xi_time_part62debb_finite_prime_support_localized_axis_threshold
    (T a b : ℕ) : XiTimePart62debbFinitePrimeSupportLocalizedAxisThresholdStatement T a b := by
  refine ⟨by simp [xiLocalizedAxisMinimalChannel], ⟨Equiv.refl _⟩, ⟨Equiv.refl _⟩, ?_⟩
  simp [xiLocalizedAxisThreshold, xiLocalizedAxisMinimalChannel]

end Omega.Zeta
