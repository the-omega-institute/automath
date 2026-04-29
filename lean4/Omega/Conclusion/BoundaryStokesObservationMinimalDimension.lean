import Mathlib.Data.Fintype.Card
import Omega.Conclusion.BoundaryStokesStrictLinearHolography

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: separating all boundary images requires at least `2^(mn)` scalar
    coordinates.
    thm:conclusion-boundary-stokes-observation-minimal-dimension -/
theorem paper_conclusion_boundary_stokes_observation_minimal_dimension_seeds
    (m n L : Nat) (f : Fin (2 ^ (m * n)) → Fin L) (hf : Function.Injective f) :
    2 ^ (m * n) ≤ L := by
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- Paper label: `thm:conclusion-boundary-stokes-observation-minimal-dimension`. The counting
argument gives the lower bound on observation dimension, and the strict linear holography theorem
supplies sharpness via a bijective `2^(mn)`-coordinate model. -/
theorem paper_conclusion_boundary_stokes_observation_minimal_dimension
    (m n L : ℕ) (f : Fin (2 ^ (m * n)) → Fin L) (hf : Function.Injective f) :
    2 ^ (m * n) ≤ L ∧ Function.Bijective (boundaryStokesStrictLinearHolography m n) := by
  refine ⟨paper_conclusion_boundary_stokes_observation_minimal_dimension_seeds m n L f hf, ?_⟩
  exact (paper_conclusion_boundary_stokes_strict_linear_holography m n).2

end Omega.Conclusion
