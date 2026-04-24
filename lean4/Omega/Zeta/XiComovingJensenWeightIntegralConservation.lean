import Omega.Zeta.XiLogDefectAffineReproducingMomentIdentities

namespace Omega.Zeta

/-- Total mass of the comoving single-defect Jensen weight. -/
noncomputable def xi_comoving_jensen_weight_integral_conservation_total_mass
    (gamma delta : ℝ) : ℝ :=
  xiLogdefectAffineZerothMoment gamma delta

/-- Paper label: `thm:xi-comoving-jensen-weight-integral-conservation`. -/
theorem paper_xi_comoving_jensen_weight_integral_conservation
    (gamma delta : ℝ) (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    xi_comoving_jensen_weight_integral_conservation_total_mass gamma delta = 2 * Real.pi * delta := by
  let _ := hdelta0
  let _ := hdelta1
  simpa [xi_comoving_jensen_weight_integral_conservation_total_mass] using
    (paper_xi_logdefect_affine_reproducing_moment_identities.2.1 gamma delta)

end Omega.Zeta
