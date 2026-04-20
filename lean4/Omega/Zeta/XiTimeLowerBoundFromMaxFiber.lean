import Mathlib
import Omega.Zeta.XiTimeFiberMinimalDimension

namespace Omega.Zeta

/-- A maximal fiber witness forces any time-register realization to have at least that many
states. This is the direct lower-bound corollary of the minimal-dimension theorem.
    thm:xi-time-lower-bound-from-max-fiber -/
theorem paper_xi_time_lower_bound_from_max_fiber
    {Ω X : Type*} [Fintype Ω] (Fold : Ω → X) (D t A : ℕ)
    (hmax : ∀ x, Nat.card (LayerFiber Fold x) ≤ D)
    (hwit : ∃ x, Nat.card (LayerFiber Fold x) = D)
    (hrealize : XiTimeRegisterRealization Fold (A ^ t)) : D ≤ A ^ t := by
  exact (paper_xi_time_fiber_minimal_dimension Fold D (A ^ t) hmax hwit).1.mp hrealize

end Omega.Zeta
