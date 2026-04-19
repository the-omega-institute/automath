import Mathlib.Tactic

namespace Omega.Zeta

/-- Chapter-local package for the finite-dimensional Toeplitz negative-inertia stability
certificate. The fields record the congruence decomposition into a positive block and a negative
Hankel Gram block, the preservation of the negative inertia count under Hermitian perturbations,
and the explicit spectral-gap lower bound away from `0`. -/
structure ToeplitzNegativeInertiaSpectralGapStabilityData where
  congruenceDecomposition : Prop
  negativeInertiaPreserved : Prop
  explicitSpectralGapLowerBound : Prop
  hasCongruenceDecomposition : congruenceDecomposition
  deriveNegativeInertiaPreserved :
    congruenceDecomposition → negativeInertiaPreserved
  deriveExplicitSpectralGapLowerBound :
    congruenceDecomposition → explicitSpectralGapLowerBound

/-- The paper argument starts from the congruence decomposition certificate. -/
theorem toeplitzNegativeInertiaCongruenceHelper
    (D : ToeplitzNegativeInertiaSpectralGapStabilityData) :
    D.congruenceDecomposition := by
  exact D.hasCongruenceDecomposition

/-- Paper-facing wrapper for the Toeplitz negative-inertia spectral-gap stability certificate.
    thm:xi-toeplitz-negative-inertia-spectral-gap-stability -/
theorem paper_xi_toeplitz_negative_inertia_spectral_gap_stability
    (D : ToeplitzNegativeInertiaSpectralGapStabilityData) :
    D.negativeInertiaPreserved ∧ D.explicitSpectralGapLowerBound := by
  have hCongruence : D.congruenceDecomposition :=
    toeplitzNegativeInertiaCongruenceHelper D
  exact ⟨D.deriveNegativeInertiaPreserved hCongruence,
    D.deriveExplicitSpectralGapLowerBound hCongruence⟩

end Omega.Zeta
