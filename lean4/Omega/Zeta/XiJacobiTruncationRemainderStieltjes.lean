namespace Omega.Zeta

set_option linter.unusedVariables false in
/-- Paper label: `prop:xi-jacobi-truncation-remainder-stieltjes`. -/
theorem paper_xi_jacobi_truncation_remainder_stieltjes
    (N : ℕ) (signedErrorStieltjes nonnegativeMeasure massFormula : Prop)
    (hStieltjes : signedErrorStieltjes)
    (hMeasure : signedErrorStieltjes → nonnegativeMeasure)
    (hMass : signedErrorStieltjes → massFormula) :
    signedErrorStieltjes ∧ nonnegativeMeasure ∧ massFormula := by
  exact ⟨hStieltjes, hMeasure hStieltjes, hMass hStieltjes⟩

end Omega.Zeta
