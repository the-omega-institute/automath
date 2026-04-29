import Omega.Zeta.XiFiberSpectrumFiniteMomentRigidity

namespace Omega.Zeta

/-- The Hankel--Vandermonde coordinate recovery package exposes the finite moment rigidity
statement with the paper label for the explicit reconstruction corollary.
    cor:xi-fiber-spectrum-hankel-vandermonde-explicit-recovery -/
theorem paper_xi_fiber_spectrum_hankel_vandermonde_explicit_recovery
    (D : FiberSpectrumMomentData) :
    D.momentExpansion ∧ D.rationalGeneratingFunction ∧ D.uniqueRecoveryFromFirstMoments := by
  exact paper_xi_fiber_spectrum_finite_moment_rigidity D

end Omega.Zeta
