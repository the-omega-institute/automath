import Mathlib.Tactic
import Omega.Folding.Entropy

open scoped goldenRatio

namespace Omega.POM

noncomputable section

/-- Multiplicative Fibonacci multiplicity attached to a composition. -/
def pomMultiplicityReal (ls : List Nat) : ℝ :=
  (ls.map fun l => (Nat.fib (l + 2) : ℝ)).prod

/-- Paper-facing Binet expansion package for the multiplicity product. -/
def multiplicityBinetTwoParameterNormalFormStatement (ls : List Nat) : Prop :=
  pomMultiplicityReal ls =
      (ls.map fun l =>
        (Real.goldenRatio ^ (l + 2) - Real.goldenConj ^ (l + 2)) / Real.sqrt 5).prod ∧
    ∀ l ∈ ls, |Real.goldenConj ^ (l + 2) / Real.sqrt 5| < 1 / 2

/-- Paper label: `prop:pom-multiplicity-binet-two-parameter-normal-form`. -/
theorem paper_pom_multiplicity_binet_two_parameter_normal_form
    (ls : List Nat) (hpos : ∀ l ∈ ls, 1 ≤ l) :
    multiplicityBinetTwoParameterNormalFormStatement ls := by
  constructor
  · induction ls with
    | nil =>
        simp [pomMultiplicityReal]
    | cons l tl _ =>
        simp [pomMultiplicityReal, Omega.Entropy.binet_formula]
  · intro l hl
    simpa using Omega.Entropy.abs_psi_pow_div_sqrt5_lt_half (l + 2)

end
end Omega.POM
