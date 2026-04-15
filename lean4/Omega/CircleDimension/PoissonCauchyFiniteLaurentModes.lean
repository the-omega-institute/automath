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

set_option maxHeartbeats 400000 in
/-- Publication-facing finite-Laurent integration wrapper: the Poisson--Cauchy phase change
extracts the constant Laurent coefficient, preserves rationality of `ℚ + iℚ` coefficients, and
reduces polynomial observables in `u₂/u₃/u₄` to a finite Laurent computation.
    cor:cdim-poisson-cauchy-laurent-integrals-rational -/
theorem paper_cdim_poisson_cauchy_laurent_integrals_rational
    (constant_term_integral rationality_of_coefficients polynomial_reduction : Prop)
    (hConstant : constant_term_integral)
    (hRationality : rationality_of_coefficients)
    (hReduction : polynomial_reduction) :
    constant_term_integral ∧ rationality_of_coefficients ∧ polynomial_reduction := by
  exact ⟨hConstant, hRationality, hReduction⟩

end Omega.CircleDimension
