import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete resultant package for the Widom certificate. The `y`-resultant is represented by a
specific integer value, the polynomial and its derivative are represented by concrete evaluation
functions, and the textbook resultant degree estimate is packaged in terms of the recorded
`y`-degrees. -/
structure conclusion_widom_resultant_certificate_degree_bound_data where
  n : ℕ
  m : ℕ
  degreeD : ℕ
  degreeDerivative : ℕ
  resultantDegree : ℕ
  resultantValue : ℤ
  polynomialValue : ℤ → ℤ
  derivativeValue : ℤ → ℤ
  degreeD_eq : degreeD = n
  degreeDerivative_eq : degreeDerivative = n - 1
  resultant_zero_iff :
    resultantValue = 0 ↔ ∃ y : ℤ, polynomialValue y = 0 ∧ derivativeValue y = 0
  textbook_resultant_degree_bound :
    resultantDegree ≤ (degreeD + degreeDerivative) * m

namespace conclusion_widom_resultant_certificate_degree_bound_data

/-- `Res_y(D, ∂D/∂y) = 0` exactly when `D` and its derivative share a root. -/
def simple_root_criterion
    (h : conclusion_widom_resultant_certificate_degree_bound_data) : Prop :=
  h.resultantValue = 0 ↔ ∃ y : ℤ, h.polynomialValue y = 0 ∧ h.derivativeValue y = 0

/-- The resultant degree in the parameter direction is bounded by `(2 n - 1) m`. -/
def resultant_degree_bound
    (h : conclusion_widom_resultant_certificate_degree_bound_data) : Prop :=
  h.resultantDegree ≤ (2 * h.n - 1) * h.m

end conclusion_widom_resultant_certificate_degree_bound_data

/-- Paper label: `prop:conclusion-widom-resultant-certificate-degree-bound`. The standard
resultant criterion gives the common-root characterization, and the textbook degree estimate for
`Res_y(D, ∂D/∂y)` specializes to the bound `(2 n - 1) m`. -/
theorem paper_conclusion_widom_resultant_certificate_degree_bound
    (h : conclusion_widom_resultant_certificate_degree_bound_data) :
    h.simple_root_criterion /\ h.resultant_degree_bound := by
  refine ⟨h.resultant_zero_iff, ?_⟩
  dsimp [conclusion_widom_resultant_certificate_degree_bound_data.resultant_degree_bound]
  have hsum : h.degreeD + h.degreeDerivative = 2 * h.n - 1 := by
    rw [h.degreeD_eq, h.degreeDerivative_eq]
    omega
  calc
    h.resultantDegree ≤ (h.degreeD + h.degreeDerivative) * h.m :=
      h.textbook_resultant_degree_bound
    _ = (2 * h.n - 1) * h.m := by
      rw [hsum]

end Omega.Conclusion
