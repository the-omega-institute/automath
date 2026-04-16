import Omega.Folding.LocalRewriteLdpBarrier

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the `Omega(m log m)` prime-register bitlength lower bound.
    cor:fold-prime-register-bitlength-omega-mlogm -/
theorem paper_fold_prime_register_bitlength_omega_mlogm
    (pairwiseCoprimeSupport primorialLowerBound rewriteDensityLowerBound
      bitlengthOmegaMlogm : Prop)
    (hCoprime : pairwiseCoprimeSupport)
    (hPrimorial : pairwiseCoprimeSupport -> primorialLowerBound)
    (hDensity : rewriteDensityLowerBound)
    (hLower : primorialLowerBound -> rewriteDensityLowerBound -> bitlengthOmegaMlogm) :
    bitlengthOmegaMlogm := by
  exact hLower (hPrimorial hCoprime) hDensity

end Omega.Folding
