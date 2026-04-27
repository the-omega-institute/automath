import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-observable-minpoly-discriminant-ramification-q9-13`.  The audited
discriminant data and quadratic-field nontriviality are retained, and repeat ramification outside
the listed bad primes contradicts the squarefreeness guarantee. -/
theorem paper_pom_observable_minpoly_discriminant_ramification_q9_13
    (q : ℕ) (DiscListed NontrivialQuadraticField : Prop)
    (Bad SquarefreeMod RepeatRamification : ℕ → ℕ → Prop)
    (hWindow : q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 13)
    (hDisc : DiscListed)
    (hField : NontrivialQuadraticField)
    (hsqfree : ∀ p, Nat.Prime p → ¬ Bad q p → SquarefreeMod q p)
    (hrepeat : ∀ p, Nat.Prime p → RepeatRamification q p → ¬ SquarefreeMod q p) :
    DiscListed ∧ NontrivialQuadraticField ∧
      ∀ p, Nat.Prime p → RepeatRamification q p → Bad q p := by
  have _ : q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 13 := hWindow
  refine ⟨hDisc, hField, ?_⟩
  intro p hp hram
  by_contra hbad
  exact hrepeat p hp hram (hsqfree p hp hbad)

end Omega.POM
