import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete moment data for the Poisson--Cauchy `I_1` seventh-order expansion. -/
structure conclusion_poisson_cauchy_i1_seventh_order_expansion_data where
  conclusion_poisson_cauchy_i1_seventh_order_expansion_mu2 : ℝ
  conclusion_poisson_cauchy_i1_seventh_order_expansion_mu3 : ℝ
  conclusion_poisson_cauchy_i1_seventh_order_expansion_mu4 : ℝ

/-- The fourth-order KL coefficient from the sixth-order expansion. -/
def conclusion_poisson_cauchy_i1_seventh_order_expansion_klFourth
    (D : conclusion_poisson_cauchy_i1_seventh_order_expansion_data) : ℝ :=
  D.conclusion_poisson_cauchy_i1_seventh_order_expansion_mu2 ^ 2 / 8

/-- The sixth-order KL coefficient from the sixth-order expansion. -/
def conclusion_poisson_cauchy_i1_seventh_order_expansion_klSixth
    (D : conclusion_poisson_cauchy_i1_seventh_order_expansion_data) : ℝ :=
  D.conclusion_poisson_cauchy_i1_seventh_order_expansion_mu2 ^ 3 / 64 -
    D.conclusion_poisson_cauchy_i1_seventh_order_expansion_mu2 *
      D.conclusion_poisson_cauchy_i1_seventh_order_expansion_mu4 / 8 +
      3 * D.conclusion_poisson_cauchy_i1_seventh_order_expansion_mu3 ^ 2 / 32

/-- The leading `I_1` coefficient obtained by differentiating `t⁻⁴` and changing sign. -/
def conclusion_poisson_cauchy_i1_seventh_order_expansion_i1Fifth
    (D : conclusion_poisson_cauchy_i1_seventh_order_expansion_data) : ℝ :=
  4 * conclusion_poisson_cauchy_i1_seventh_order_expansion_klFourth D

/-- The seventh-order `I_1` coefficient obtained by differentiating `t⁻⁶` and changing sign. -/
def conclusion_poisson_cauchy_i1_seventh_order_expansion_i1Seventh
    (D : conclusion_poisson_cauchy_i1_seventh_order_expansion_data) : ℝ :=
  6 * conclusion_poisson_cauchy_i1_seventh_order_expansion_klSixth D

/-- Paper-facing coefficient statement for the seventh-order `I_1` expansion. -/
def conclusion_poisson_cauchy_i1_seventh_order_expansion_statement
    (D : conclusion_poisson_cauchy_i1_seventh_order_expansion_data) : Prop :=
  conclusion_poisson_cauchy_i1_seventh_order_expansion_i1Fifth D =
      D.conclusion_poisson_cauchy_i1_seventh_order_expansion_mu2 ^ 2 / 2 ∧
    conclusion_poisson_cauchy_i1_seventh_order_expansion_i1Seventh D =
      3 * D.conclusion_poisson_cauchy_i1_seventh_order_expansion_mu2 ^ 3 / 32 -
        3 * D.conclusion_poisson_cauchy_i1_seventh_order_expansion_mu2 *
          D.conclusion_poisson_cauchy_i1_seventh_order_expansion_mu4 / 4 +
          9 * D.conclusion_poisson_cauchy_i1_seventh_order_expansion_mu3 ^ 2 / 16

/-- Paper label: `cor:conclusion-poisson-cauchy-i1-seventh-order-expansion`. -/
theorem paper_conclusion_poisson_cauchy_i1_seventh_order_expansion
    (D : conclusion_poisson_cauchy_i1_seventh_order_expansion_data) :
    conclusion_poisson_cauchy_i1_seventh_order_expansion_statement D := by
  constructor
  · dsimp [conclusion_poisson_cauchy_i1_seventh_order_expansion_i1Fifth,
      conclusion_poisson_cauchy_i1_seventh_order_expansion_klFourth]
    ring
  · dsimp [conclusion_poisson_cauchy_i1_seventh_order_expansion_i1Seventh,
      conclusion_poisson_cauchy_i1_seventh_order_expansion_klSixth]
    ring

end

end Omega.Conclusion
