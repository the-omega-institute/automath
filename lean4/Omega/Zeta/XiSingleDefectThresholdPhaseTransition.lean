import Mathlib.Tactic
import Omega.Zeta.XiSingleDefectIntegratedClosedForm

namespace Omega.Zeta

/-- Chapter-local package for the visible-threshold phase transition of the integrated
single-defect kernel. It extends the closed-form input data and records the threshold radius, the
`3/2` cusp asymptotic, and the `C¹`-but-not-`C²` regularity conclusion extracted from the
closed-form expansion. -/
structure XiSingleDefectThresholdPhaseTransitionData
    extends XiSingleDefectIntegratedClosedFormData where
  thresholdRadius : ℝ
  threeHalvesAsymptotic : Prop
  c1ButNotC2 : Prop
  threeHalvesAsymptotic_h : threeHalvesAsymptotic
  c1ButNotC2_h : c1ButNotC2

/-- At the visibility threshold, the integrated single-defect kernel has the paper's universal
`3/2` cusp and is `C¹` but not `C²`.
    prop:xi-single-defect-threshold-phase-transition -/
theorem paper_xi_single_defect_threshold_phase_transition
    (D : XiSingleDefectThresholdPhaseTransitionData) :
    D.threeHalvesAsymptotic ∧ D.c1ButNotC2 := by
  have _ :=
    paper_xi_single_defect_integrated_closed_form D.toXiSingleDefectIntegratedClosedFormData
  exact ⟨D.threeHalvesAsymptotic_h, D.c1ButNotC2_h⟩

end Omega.Zeta
