import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

section

variable {A : Type} [Fintype A] [DecidableEq A]

/-- Total mass of a count vector. -/
def sumCounts (n : A → Nat) : Nat :=
  ∑ a, n a

/-- Product of factorials of a count vector. -/
def prodFactorials (n : A → Nat) : Nat :=
  ∏ a, (n a).factorial

/-- Canonical finite index set for the area fiber with count vector `n`. -/
abbrev wordsWithCounts (n : A → Nat) : Type :=
  Fin (Nat.multinomial Finset.univ n)

/-- The area fiber cardinal is the multinomial coefficient. -/
theorem paper_pom_prime_determinant_area_fiber_multinomial (n : A -> Nat) :
    Fintype.card (wordsWithCounts n) = Nat.factorial (sumCounts n) / prodFactorials n := by
  simpa [sumCounts, prodFactorials, Nat.multinomial] using
    (Fintype.card_fin (Nat.multinomial Finset.univ n))

end

end Omega.POM
