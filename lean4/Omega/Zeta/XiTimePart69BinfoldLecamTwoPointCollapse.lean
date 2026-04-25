import Mathlib.Tactic
import Omega.GU.Window6BinfoldLastbitLecamEquivalence

namespace Omega.Zeta

/-- Chapter-local total-variation discrepancy between the original block statistic and its last-bit
proxy. -/
def xi_time_part69_binfold_lecam_two_point_collapse_discrepancy
    (d : Omega.GU.Window6BinfoldLastbitLeCamData) : Real :=
  abs (d.tvMuUniform - d.tvLastbitUniform)

/-- Concrete wrapper for the two-point-collapse bound: the original experiment and the last-bit
proxy differ by at most twice the block-uniform proxy error, hence by the same exponential rate. -/
def xi_time_part69_binfold_lecam_two_point_collapse_statement : Prop :=
  ∀ d : Omega.GU.Window6BinfoldLastbitLeCamData,
    xi_time_part69_binfold_lecam_two_point_collapse_discrepancy d <= 2 * d.tvMuBlockUniform ∧
      xi_time_part69_binfold_lecam_two_point_collapse_discrepancy d <=
        2 * d.C * (d.phi / 2) ^ d.m

/-- Paper label: `thm:xi-time-part69-binfold-lecam-two-point-collapse`. -/
theorem paper_xi_time_part69_binfold_lecam_two_point_collapse :
    xi_time_part69_binfold_lecam_two_point_collapse_statement := by
  intro d
  simpa [xi_time_part69_binfold_lecam_two_point_collapse_discrepancy] using
    Omega.GU.paper_window6_binfold_lastbit_lecam_equivalence d

end Omega.Zeta
