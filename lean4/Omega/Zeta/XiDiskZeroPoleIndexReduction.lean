import Omega.UnitCirclePhaseArithmetic.AppRhIffDiskZeroFree
import Omega.Zeta.XiCompletedPolynomialPontryaginIndex
import Omega.Zeta.XiToeplitzInertiaStabilizesToKappa

namespace Omega.Zeta

noncomputable section

/-- Paper label: `thm:xi-disk-zero-pole-index-reduction`. -/
theorem paper_xi_disk_zero_pole_index_reduction
    (D : Omega.UnitCirclePhaseArithmetic.AppRhIffDiskZeroFreeData) (roots : List (ℂ × ℕ)) :
    (D.riemannHypothesis ↔ D.diskZeroFree) ∧
      (Omega.Zeta.xi_phiL_negative_squares_equals_disk_roots_horizonPoleCount roots =
        Omega.Zeta.xi_phiL_negative_squares_equals_disk_roots_kappa roots) ∧
      Omega.Zeta.xi_toeplitz_inertia_stabilizes_to_kappa_statement := by
  refine ⟨Omega.UnitCirclePhaseArithmetic.paper_app_rh_iff_disk_zero_free D, ?_, ?_⟩
  · exact (paper_xi_phil_negative_squares_equals_disk_roots roots).1
  · exact paper_xi_toeplitz_inertia_stabilizes_to_kappa

end

end Omega.Zeta
