import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the oracle-success strong converse. The function `Xi` is supplied by the
previous variational formula as the negative of a nonnegative rate function; the typical exponent is
the unique zero of that rate, and rates are strictly positive below it. -/
structure conclusion_oracle_success_strong_converse_data where
  conclusion_oracle_success_strong_converse_Xi : ℝ → ℝ
  conclusion_oracle_success_strong_converse_rate : ℝ → ℝ
  conclusion_oracle_success_strong_converse_typicalExponent : ℝ
  conclusion_oracle_success_strong_converse_variational_formula :
    ∀ β,
      conclusion_oracle_success_strong_converse_Xi β =
        -conclusion_oracle_success_strong_converse_rate β
  conclusion_oracle_success_strong_converse_rate_nonneg :
    ∀ β, 0 ≤ conclusion_oracle_success_strong_converse_rate β
  conclusion_oracle_success_strong_converse_rate_zero_iff :
    ∀ β,
      conclusion_oracle_success_strong_converse_rate β = 0 ↔
        β = conclusion_oracle_success_strong_converse_typicalExponent
  conclusion_oracle_success_strong_converse_rate_pos_below :
    ∀ β,
      β < conclusion_oracle_success_strong_converse_typicalExponent →
        0 < conclusion_oracle_success_strong_converse_rate β

/-- `Xi(beta)=0` is exactly the nonnegative rate-function zero-set condition. -/
def conclusion_oracle_success_strong_converse_zero_set
    (D : conclusion_oracle_success_strong_converse_data) : Prop :=
  ∀ β,
    D.conclusion_oracle_success_strong_converse_Xi β = 0 ↔
      D.conclusion_oracle_success_strong_converse_rate β = 0

/-- Below the typical exponent, the variational exponent is strictly negative. -/
def conclusion_oracle_success_strong_converse_strict_negativity
    (D : conclusion_oracle_success_strong_converse_data) : Prop :=
  ∀ β,
    β < D.conclusion_oracle_success_strong_converse_typicalExponent →
      D.conclusion_oracle_success_strong_converse_Xi β < 0

/-- Combined paper-facing claim. -/
def conclusion_oracle_success_strong_converse_claim
    (D : conclusion_oracle_success_strong_converse_data) : Prop :=
  conclusion_oracle_success_strong_converse_zero_set D ∧
    conclusion_oracle_success_strong_converse_strict_negativity D

/-- Paper label: `cor:conclusion-oracle-success-strong-converse`. -/
theorem paper_conclusion_oracle_success_strong_converse
    (D : conclusion_oracle_success_strong_converse_data) :
    conclusion_oracle_success_strong_converse_claim D := by
  refine ⟨?_, ?_⟩
  · intro β
    rw [D.conclusion_oracle_success_strong_converse_variational_formula β]
    constructor
    · intro h
      exact neg_eq_zero.mp h
    · intro h
      simp [h]
  · intro β hβ
    rw [D.conclusion_oracle_success_strong_converse_variational_formula β]
    exact neg_neg_of_pos
      (D.conclusion_oracle_success_strong_converse_rate_pos_below β hβ)

end Omega.Conclusion
