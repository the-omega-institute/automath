import Omega.Conclusion.BoundaryStokesObservationMinimalDimension
import Omega.Conclusion.BoundaryStokesStrictLinearHolography

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- Exact-vs-isotropic anisotropy gap: the strict linear holography map is bijective, while any
    injective linear readout still needs at least `2^(m*n)` coordinates.
    thm:conclusion-exact-holography-vs-isotropic-tomography-anisotropy-gap -/
theorem paper_conclusion_exact_holography_vs_isotropic_tomography_anisotropy_gap
    (m n L : Nat) (f : Fin (2 ^ (m * n)) → Fin L) (hf : Function.Injective f) :
    Function.Bijective (boundaryStokesStrictLinearHolography m n) ∧ 2 ^ (m * n) ≤ L := by
  refine ⟨(paper_conclusion_boundary_stokes_strict_linear_holography m n).2, ?_⟩
  exact paper_conclusion_boundary_stokes_observation_minimal_dimension_seeds m n L f hf

end Omega.Conclusion
