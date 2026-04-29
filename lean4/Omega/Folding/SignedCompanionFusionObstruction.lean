import Omega.Folding.SignedCompanionLucasCertificate

namespace Omega

/-- Paper label: `cor:signed-companion-fusion-obstruction`. -/
theorem paper_signed_companion_fusion_obstruction :
    signed_companion_lucas_certificate_secondCoeff 6 ≠ (lucasNum 6 : Int) := by
  norm_num [signed_companion_lucas_certificate_secondCoeff,
    signed_companion_lucas_certificate_coeffs, lucasNum]

end Omega
