import Omega.Zeta.ToeplitzNegativeInertiaSpectralGapStability

namespace Omega.Zeta

/-- Paper-facing corollary exposing the finite Toeplitz-to-Hankel congruence certificate.
    cor:xi-toeplitz-scan-hankel-congruence-decomposition -/
theorem paper_xi_toeplitz_scan_hankel_congruence_decomposition
    (D : ToeplitzNegativeInertiaSpectralGapStabilityData) :
    D.congruenceDecomposition := by
  exact toeplitzNegativeInertiaCongruenceHelper D

end Omega.Zeta
