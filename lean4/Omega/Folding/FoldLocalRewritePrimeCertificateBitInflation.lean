import Omega.Folding.FoldPrimeRegisterBitlengthOmegaMlogm

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the `Omega(m log m)` bit inflation of prime-register certificates
    induced by the local rewrite lower-tail barrier and one-prime-per-step encodings.
    cor:fold-local-rewrite-prime-certificate-bit-inflation -/
theorem paper_fold_local_rewrite_prime_certificate_bit_inflation
    (localRewriteLowerTail primeRegisterEncoding primeCertificateBitInflation : Prop)
    (hTail : localRewriteLowerTail)
    (hEncoding : primeRegisterEncoding)
    (hInflation :
      localRewriteLowerTail -> primeRegisterEncoding -> primeCertificateBitInflation) :
    primeCertificateBitInflation := by
  exact hInflation hTail hEncoding

end Omega.Folding
