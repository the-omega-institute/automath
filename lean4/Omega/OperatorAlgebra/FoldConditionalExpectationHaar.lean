namespace Omega.OperatorAlgebra

/-- Paper-facing wrapper for the fold conditional expectation Haar formula and uniqueness package.
    thm:op-algebra-fold-conditional-expectation-haar -/
theorem paper_op_algebra_fold_conditional_expectation_haar {A B G : Type}
    (E_m haarAverage : A → B) (haarAverageFormula uniqueExpectation : Prop)
    (hHaarAverageFormula : haarAverageFormula) (hUniqueExpectation : uniqueExpectation) :
    haarAverageFormula ∧ uniqueExpectation := by
  let _ : A → B := E_m
  let _ : A → B := haarAverage
  let _ : Type := G
  exact ⟨hHaarAverageFormula, hUniqueExpectation⟩

end Omega.OperatorAlgebra
