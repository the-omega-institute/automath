import Mathlib.Data.Fintype.Card

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: separating all boundary images requires at least `2^(mn)` scalar
    coordinates.
    thm:conclusion-boundary-stokes-observation-minimal-dimension -/
theorem paper_conclusion_boundary_stokes_observation_minimal_dimension_seeds
    (m n L : Nat) (f : Fin (2 ^ (m * n)) → Fin L) (hf : Function.Injective f) :
    2 ^ (m * n) ≤ L := by
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective f hf

end Omega.Conclusion
