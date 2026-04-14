import Mathlib.LinearAlgebra.Span.Basic

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the cyclic-quotient span lemma in the ETDS
    finite-group shadow section.
    lem:cyclic-quotients-one-dimensional-characters -/
theorem paper_etds_cyclic_quotients_one_dimensional_characters
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (cyclicPullbacks oneDimensional : Set V)
    (hforward : ∀ ⦃v : V⦄, v ∈ cyclicPullbacks → v ∈ oneDimensional)
    (hbackward : ∀ ⦃v : V⦄, v ∈ oneDimensional → v ∈ cyclicPullbacks) :
    Submodule.span K cyclicPullbacks = Submodule.span K oneDimensional := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun v hv => Submodule.subset_span (hforward hv))
  · exact Submodule.span_le.mpr (fun v hv => Submodule.subset_span (hbackward hv))

end Omega.Zeta
