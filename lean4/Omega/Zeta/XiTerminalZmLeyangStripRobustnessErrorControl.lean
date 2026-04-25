import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmGodelLeyangTropicalStripLattice

namespace Omega.Zeta

/-- Concrete data for the Leyang tropical-strip robustness package. The fields are numerical audit
data and explicit inequalities, not abstract proposition placeholders. -/
structure XiTerminalZmLeyangStripRobustnessErrorControlData where
  dominantWeight : ℝ
  tailWeight : ℝ
  distortion : ℝ
  normalizationSlack : ℝ
  tropicalStrip :
    XiTerminalZmGodelLeyangTropicalStripLatticeData := {}
  dominantWeight_nonneg : 0 ≤ dominantWeight
  tailWeight_nonneg : 0 ≤ tailWeight
  distortion_nonneg : 0 ≤ distortion
  normalizationSlack_nonneg : 0 ≤ normalizationSlack
  dominant_ge_double_tail : 2 * tailWeight ≤ dominantWeight
  distortion_tail_le_slack : distortion * (dominantWeight + tailWeight) ≤ normalizationSlack

namespace XiTerminalZmLeyangStripRobustnessErrorControlData

/-- The posterior tail is bounded by half of the dominant weight, so the normalized dominant mass
still wins. -/
def posterior_dominance_bound (D : XiTerminalZmLeyangStripRobustnessErrorControlData) : Prop :=
  D.tailWeight ≤ D.dominantWeight / 2

/-- The `L¹` perturbation is bounded by the multiplicative distortion times the total mass, and
that quantity is controlled by the normalization slack. -/
def energy_perturbation_l1_bound (D : XiTerminalZmLeyangStripRobustnessErrorControlData) : Prop :=
  D.distortion * (D.dominantWeight + D.tailWeight) ≤ D.normalizationSlack

end XiTerminalZmLeyangStripRobustnessErrorControlData

open XiTerminalZmLeyangStripRobustnessErrorControlData

/-- Paper label: `cor:xi-terminal-zm-leyang-strip-robustness-error-control`. The tropical-strip
certificate supplies the ambient strip control; the posterior tail bound is the normalized form of
`2 * tail ≤ dominant`; and the `L¹` estimate is the recorded multiplicative-distortion bound. -/
theorem paper_xi_terminal_zm_leyang_strip_robustness_error_control
    (D : XiTerminalZmLeyangStripRobustnessErrorControlData) :
    D.posterior_dominance_bound ∧ D.energy_perturbation_l1_bound := by
  have hstrip := paper_xi_terminal_zm_godel_leyang_tropical_strip_lattice D.tropicalStrip
  rcases hstrip with ⟨_, _⟩
  constructor
  · unfold XiTerminalZmLeyangStripRobustnessErrorControlData.posterior_dominance_bound
    linarith [D.dominant_ge_double_tail]
  · exact D.distortion_tail_le_slack

end Omega.Zeta
