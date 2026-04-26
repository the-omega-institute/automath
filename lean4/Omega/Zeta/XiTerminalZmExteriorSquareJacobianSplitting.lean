import Omega.CircleDimension.S4V4JacobianPullbackKernelPrymSplitting
import Omega.Zeta.XiTerminalZmExteriorSquareCurveGenus2
import Omega.Zeta.XiTerminalZmS3EndoscopicHomologyA2Identification

namespace Omega.Zeta

open Omega.CircleDimension

/-- Paper label: `cor:xi-terminal-zm-exterior-square-jacobian-splitting`.
The exterior-square curve is already packaged as a genus-two cover, the relevant `V₄` Prym data
is the audited `A₂`-polarized package, and the terminal endoscopic wrapper records the resulting
elliptic-product Jacobian splitting. -/
theorem paper_xi_terminal_zm_exterior_square_jacobian_splitting :
    xi_terminal_zm_exterior_square_curve_genus2_statement ∧
      (let D := cdim_s4_v4_jacobian_pullback_kernel_and_prym_splitting_prym_data
       D.standardGeneratorExists ∧ D.invariantPolarizationsAreA2 ∧ D.naturalPrymPolarizationIsA2) ∧
      xiTerminalZmS3JacobianSplitting := by
  have hCurve := paper_xi_terminal_zm_exterior_square_curve_genus2
  have hV4 := paper_cdim_s4_v4_jacobian_pullback_kernel_and_prym_splitting
  rcases paper_xi_terminal_zm_s3_endoscopic_homology_a2_identification with ⟨_, _, hSplit⟩
  exact ⟨hCurve, hV4.2.1, hSplit⟩

end Omega.Zeta
