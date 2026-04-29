import Omega.Conclusion.CanonicalSliceExactFixedpointCount

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9g-canonical-fixed-point-badic-periodic`.
In the canonical slice model, the fixed point associated to a digit block is the block itself. -/
theorem paper_xi_time_part9g_canonical_fixed_point_badic_periodic
    (D : Omega.Conclusion.CanonicalSliceData) (k : Nat) (_hk : 1 ≤ k)
    (r : D.fixedPointsAtLayer k) :
    ∃! x : D.fixedPointsAtLayer k, D.IsFixedPoint r k x := by
  refine ⟨r, ?_, ?_⟩
  · simp [Omega.Conclusion.CanonicalSliceData.IsFixedPoint]
  · intro x hx
    simpa [Omega.Conclusion.CanonicalSliceData.IsFixedPoint] using hx

end Omega.Zeta
