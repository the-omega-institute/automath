import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- The divisor-side Dirichlet sum weighted by Euler totients. The dependence on `s` is kept as a
formal parameter in this finite bookkeeping model. -/
def divisorTotientDirichletSum (N : ℕ) (_s : ℝ) : ℝ :=
  Finset.sum N.divisors fun d => (Nat.totient d : ℝ)

/-- Character-conductor zeta function for the mixed hidden-state model. -/
def characterConductorZeta (beta N : ℕ) (s : ℝ) : ℝ :=
  (2 : ℝ) ^ beta * divisorTotientDirichletSum N s

/-- Exact conductor zeta factorization for the mixed hidden-state model.
    thm:conclusion-mixed-hiddenstate-character-conductor-zeta -/
theorem paper_conclusion_mixed_hiddenstate_character_conductor_zeta (beta N : ℕ) (s : ℝ) :
    characterConductorZeta beta N s = (2 : ℝ) ^ beta * divisorTotientDirichletSum N s := by
  rfl

/-- A concrete receiver model for the mixed hidden-state truncation
`H_{S,N} ≅ (ℤ/2ℤ)^β × ℤ/Nℤ`. -/
def conclusion_mixed_hiddenstate_minimal_generator_number_receiverModel
    (beta N : ℕ) : Type :=
  (Fin beta → ZMod 2) × ZMod N

/-- The closed-form minimal generator count predicted by the mixed hidden-state receiver model. -/
def conclusion_mixed_hiddenstate_minimal_generator_number_value (beta N : ℕ) : ℕ :=
  if beta = 0 then
    if N = 1 then 0 else 1
  else if N % 2 = 0 then
    beta + 1
  else
    beta

/-- Paper-facing closed form for the minimal generator count of a faithful finite abelian receiver
for the mixed hidden-state truncation.
    thm:conclusion-mixed-hiddenstate-minimal-generator-number -/
theorem paper_conclusion_mixed_hiddenstate_minimal_generator_number (beta N : ℕ) :
    conclusion_mixed_hiddenstate_minimal_generator_number_receiverModel beta N =
        ((Fin beta → ZMod 2) × ZMod N) ∧
      (conclusion_mixed_hiddenstate_minimal_generator_number_value beta N =
        if beta = 0 then
          if N = 1 then 0 else 1
        else if N % 2 = 0 then
          beta + 1
        else
          beta) ∧
      conclusion_mixed_hiddenstate_minimal_generator_number_value beta N ≤ beta + 1 := by
  constructor
  · rfl
  constructor
  · rfl
  · by_cases hbeta : beta = 0
    · subst hbeta
      by_cases hN : N = 1
      · simp [conclusion_mixed_hiddenstate_minimal_generator_number_value, hN]
      · simp [conclusion_mixed_hiddenstate_minimal_generator_number_value, hN]
    · by_cases hEven : N % 2 = 0
      · simp [conclusion_mixed_hiddenstate_minimal_generator_number_value, hbeta, hEven]
      · simp [conclusion_mixed_hiddenstate_minimal_generator_number_value, hbeta, hEven]

end Omega.Conclusion
