import Omega.POM.ProjectivePressureZeroNormalization

namespace Omega.Conclusion

/-- Concrete integer-anchor datum for
`thm:conclusion-projective-pressure-integer-algebraic-anchor`. The anchor eigenvalue/radius are
actual real numbers tied to the finite projective-pressure normalization datum. -/
structure conclusion_projective_pressure_integer_algebraic_anchor_data where
  pressureDatum : Omega.POM.ProjectivePressureDatum
  anchorEigenvalue : ℝ
  anchorRadius : ℝ
  anchorEigenvalue_eq_lambda : anchorEigenvalue = pressureDatum.lambda 1
  anchorRadius_eq_inputCard : anchorRadius = pressureDatum.inputAlphabetCard

namespace conclusion_projective_pressure_integer_algebraic_anchor_data

/-- At the integer anchor the eigenvalue and radius are the input-cardinality constant, and the
normalized pressure is the corresponding output-cardinality quotient. -/
def integer_anchor_identity
    (D : conclusion_projective_pressure_integer_algebraic_anchor_data) : Prop :=
  D.anchorEigenvalue = D.pressureDatum.inputAlphabetCard ∧
    D.anchorRadius = D.pressureDatum.inputAlphabetCard ∧
      D.pressureDatum.Lambda 0 =
        Real.log ((D.pressureDatum.inputAlphabetCard : ℝ) / D.pressureDatum.outputAlphabetCard)

end conclusion_projective_pressure_integer_algebraic_anchor_data

/-- Paper label: `thm:conclusion-projective-pressure-integer-algebraic-anchor`. -/
theorem paper_conclusion_projective_pressure_integer_algebraic_anchor
    (D : conclusion_projective_pressure_integer_algebraic_anchor_data) :
    D.integer_anchor_identity := by
  rcases Omega.POM.paper_pom_projective_pressure_zero_normalization D.pressureDatum with
    ⟨_hOnes, hLambda, hPressure⟩
  refine ⟨?_, ?_, hPressure⟩
  · exact D.anchorEigenvalue_eq_lambda.trans hLambda
  · exact D.anchorRadius_eq_inputCard

end Omega.Conclusion
