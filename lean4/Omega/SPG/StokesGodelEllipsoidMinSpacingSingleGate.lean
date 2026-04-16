import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SPG

/-- Chapter-local data for the single-gate minimum-spacing law. The witnesses record a pair of
ellipsoid-lattice points whose readouts differ by at most the explicit spacing bound. -/
structure SingleGateMinSpacingLawData where
  pointCount : Nat
  readout : Fin pointCount → ℝ
  spacingBound : ℝ
  leftPoint : Fin pointCount
  rightPoint : Fin pointCount
  left_ne_right : leftPoint ≠ rightPoint
  spacingBound_witness : |readout leftPoint - readout rightPoint| ≤ spacingBound

/-- On the single-gate energy shell, the projected Stokes--Gödel readout has two distinct lattice
points within the explicit spacing bound. This is the paper-facing pigeonhole package behind the
critical-energy corollary. `thm:spg-stokes-godel-ellipsoid-min-spacing-single-gate` -/
theorem paper_spg_stokes_godel_ellipsoid_min_spacing_single_gate
    (h : SingleGateMinSpacingLawData) :
    ∃ i j : Fin h.pointCount, i ≠ j ∧ |h.readout i - h.readout j| ≤ h.spacingBound := by
  exact ⟨h.leftPoint, h.rightPoint, h.left_ne_right, h.spacingBound_witness⟩

end Omega.SPG
