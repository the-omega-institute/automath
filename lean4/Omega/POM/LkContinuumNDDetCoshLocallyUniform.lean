import Omega.POM.LkContinuumNDDetCosh

namespace Omega.POM

open Filter Topology

noncomputable section

/-- Paper label: `cor:pom-Lk-continuum-ND-det-cosh-locally-uniform`. -/
theorem paper_pom_lk_continuum_nd_det_cosh_locally_uniform
    (D : pom_lk_continuum_nd_det_cosh_Data) :
    (∀ k : ℕ, D.smallArgumentResidual k = 0) ∧
      Tendsto D.shiftedDeterminant atTop (𝓝 D.continuumDeterminant) := by
  exact ⟨pom_lk_continuum_nd_det_cosh_small_argument_residual_zero D,
    pom_lk_continuum_nd_det_cosh_shifted_determinant_tendsto D⟩

end

end Omega.POM
