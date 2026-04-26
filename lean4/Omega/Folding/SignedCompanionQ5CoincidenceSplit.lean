import Omega.Folding.SignedCompanionLucasCertificate

namespace Omega

/-- Paper label: `cor:signed-companion-q5-coincidence-split`. -/
theorem paper_signed_companion_q5_coincidence_split :
    signed_companion_lucas_certificate_secondCoeff 5 = (lucasNum 5 : Int) ∧
      signed_companion_lucas_certificate_excess 5 = (lucasNum 5 : Int) ∧
      signed_companion_lucas_certificate_signedDet 5 - (Nat.fib 8 : Int) =
        (lucasNum 5 : Int) := by
  norm_num [signed_companion_lucas_certificate_secondCoeff,
    signed_companion_lucas_certificate_excess,
    signed_companion_lucas_certificate_signedDet,
    signed_companion_lucas_certificate_coeffs, lucasNum]

end Omega
