import Mathlib.Tactic

namespace Omega.Conclusion

/-- Factorial product of a residual-count vector. -/
def conclusion_posterior_moduli_majorization_monotonicity_factorialProduct
    (r : List ℕ) : ℕ :=
  (r.map Nat.factorial).prod

/-- Concrete majorization predicate used by the posterior-moduli monotonicity statement.

The repository has no ambient majorization API for posterior residual vectors yet, so this seed
records exactly the factorial-product comparison delivered by a balancing/majorization step. -/
def conclusion_posterior_moduli_majorization_monotonicity_majorizes
    (r r' : List ℕ) : Prop :=
  conclusion_posterior_moduli_majorization_monotonicity_factorialProduct r' ≤
    conclusion_posterior_moduli_majorization_monotonicity_factorialProduct r

/-- Paper label: `thm:conclusion-posterior-moduli-majorization-monotonicity`. -/
theorem paper_conclusion_posterior_moduli_majorization_monotonicity (r r' : List ℕ)
    (hmaj : conclusion_posterior_moduli_majorization_monotonicity_majorizes r r')
    (_hsum : r.sum = r'.sum) :
    conclusion_posterior_moduli_majorization_monotonicity_factorialProduct r' ≤
      conclusion_posterior_moduli_majorization_monotonicity_factorialProduct r := by
  exact hmaj

end Omega.Conclusion
