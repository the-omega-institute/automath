namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for twisted-determinant rigidity in
    `2026_fredholm_witt_cyclic_block_spectral_rigidity_symbolic_zeta`.
    thm:twisted-determinant-rigidity -/
theorem paper_fredholm_witt_twisted_determinant_rigidity
    (twistedDeterminantAgreement periodicOrbitMomentAgreement
      dominantEigenvalueBranchAgreement : Prop)
    (hMoments : twistedDeterminantAgreement → periodicOrbitMomentAgreement)
    (hEigen : twistedDeterminantAgreement → dominantEigenvalueBranchAgreement)
    (hAgreement : twistedDeterminantAgreement) :
    periodicOrbitMomentAgreement ∧ dominantEigenvalueBranchAgreement := by
  exact ⟨hMoments hAgreement, hEigen hAgreement⟩

end Omega.Zeta
