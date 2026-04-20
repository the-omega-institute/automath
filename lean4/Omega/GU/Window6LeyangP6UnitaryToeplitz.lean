import Omega.GU.Window6P6ToeplitzCertificateChain

namespace Omega.GU

/-- Paper-facing wrapper for the Lee--Yang / Toeplitz package on the window-`6`, `p = 6`
certificate chain: the audited pushforward data provide the selfadjoint witness, the certified
unit-circle root of the completed characteristic polynomial, and the Jensen-defect / Toeplitz-PSD
equivalences recorded by the certificate loop.
    thm:window6-leyang-p6-unitary-toeplitz -/
theorem paper_window6_leyang_p6_unitary_toeplitz
    (D : Window6P6ToeplitzCertificateChainData) :
    window6P6Selfadjoint D ∧
      window6P6FiniteCommutant D ∧
      window6P6UnitCircleRoot D ∧
      (D.certificateLoop.rh ↔ D.certificateLoop.jensenDefectZeroLimit) ∧
      (D.certificateLoop.jensenDefectZeroLimit ↔ D.certificateLoop.repulsionRadiusTendsToOne) ∧
      (D.certificateLoop.repulsionRadiusTendsToOne ↔ D.certificateLoop.toeplitzPsdAll) ∧
      (D.certificateLoop.toeplitzPsdAll ↔ D.certificateLoop.toeplitzPsdCofinal) := by
  rcases paper_window6_p6_toeplitz_certificate_chain D with
    ⟨_, hSelfadjoint, hCommutant, hRH, hJensen, hToeplitzAll, hToeplitzCofinal, _, _, _, _, _,
      _, hUnitRoot⟩
  exact ⟨hSelfadjoint, hCommutant, hUnitRoot, hRH, hJensen, hToeplitzAll, hToeplitzCofinal⟩

end Omega.GU
