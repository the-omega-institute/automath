namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for cumulant rigidity of twisted determinant data
    in `2026_fredholm_witt_cyclic_block_spectral_rigidity_symbolic_zeta`.
    cor:twisted-determinant-cumulants -/
theorem paper_fredholm_witt_twisted_determinant_cumulants
    (twistedDeterminantRigidity dominantEigenvalueAgreement cumulantAgreement
      varianceAgreement : Prop)
    (hEigen : twistedDeterminantRigidity → dominantEigenvalueAgreement)
    (hCumulants : dominantEigenvalueAgreement → cumulantAgreement)
    (hVariance : cumulantAgreement → varianceAgreement)
    (hRigid : twistedDeterminantRigidity) :
    dominantEigenvalueAgreement ∧ cumulantAgreement ∧ varianceAgreement := by
  have hDom : dominantEigenvalueAgreement := hEigen hRigid
  have hCum : cumulantAgreement := hCumulants hDom
  exact ⟨hDom, hCum, hVariance hCum⟩

end Omega.Zeta
