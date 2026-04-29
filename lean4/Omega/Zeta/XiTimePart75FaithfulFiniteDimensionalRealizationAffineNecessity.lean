import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part75-faithful-finite-dimensional-realization-affine-necessity`. -/
theorem paper_xi_time_part75_faithful_finite_dimensional_realization_affine_necessity
    (affineFaithful noFiniteCommutativeLedger homCdimInfinite implCdimHalf : Prop)
    (hAffine : affineFaithful) (hNoLedger : noFiniteCommutativeLedger)
    (hHom : noFiniteCommutativeLedger → homCdimInfinite)
    (hImpl : affineFaithful → implCdimHalf) :
    affineFaithful ∧ noFiniteCommutativeLedger ∧ homCdimInfinite ∧ implCdimHalf := by
  exact ⟨hAffine, hNoLedger, hHom hNoLedger, hImpl hAffine⟩

end Omega.Zeta
