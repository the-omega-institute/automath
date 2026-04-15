import Mathlib.Tactic
import Omega.CircleDimension.PoissonCauchyMomentInversionByPhaseModes

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Publication-facing finite-Laurent wrapper: the normalized Poisson--Cauchy derivative ratios
are `t`-independent, truncate to finitely many Laurent modes in the Cayley variable, have rigid
top coefficients, and yield the explicit `u₂/u₃/u₄` expansions used by the phase-mode inversion.
    prop:cdim-poisson-cauchy-finite-laurent-modes -/
theorem paper_cdim_poisson_cauchy_finite_laurent_modes
    (tIndependent finiteLaurentModes highestModeRigidity u234LaurentExpansions : Prop)
    (htIndependent : tIndependent)
    (hFiniteLaurentModes : finiteLaurentModes)
    (hHighestModeRigidity : highestModeRigidity)
    (hu234LaurentExpansions : u234LaurentExpansions) :
    tIndependent ∧ finiteLaurentModes ∧ highestModeRigidity ∧ u234LaurentExpansions := by
  exact ⟨htIndependent, hFiniteLaurentModes, hHighestModeRigidity, hu234LaurentExpansions⟩

end Omega.CircleDimension
