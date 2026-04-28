import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-leyang-finite-kernel-algebraic-vs-transcendental-layering`. -/
theorem paper_xi_leyang_finite_kernel_algebraic_vs_transcendental_layering
    (derivativesAlgebraic entropyTranscendental layerSeparation : Prop)
    (hder : derivativesAlgebraic) (hent : entropyTranscendental)
    (hsep : derivativesAlgebraic → entropyTranscendental → layerSeparation) :
    derivativesAlgebraic ∧ entropyTranscendental ∧ layerSeparation := by
  exact ⟨hder, hent, hsep hder hent⟩

end Omega.Zeta
