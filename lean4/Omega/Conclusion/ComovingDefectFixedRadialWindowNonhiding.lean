import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete comoving-profile data for a finite family of point defects in a fixed radial window. -/
structure ComovingDefectFixedRadialWindowNonhidingData where
  κ : ℕ
  delta : Fin κ → ℝ
  l1Norm : ℝ
  linfNorm : ℝ
  deltaMinus : ℝ
  deltaPlus : ℝ
  l1Formula :
    l1Norm = 4 * Real.pi * ∑ j : Fin κ, delta j / (1 + delta j)
  l1SummandLower :
    ∀ j : Fin κ, deltaMinus / (1 + deltaPlus) ≤ delta j / (1 + delta j)
  linfRatioLower :
    2 * deltaMinus ^ 2 * (1 + deltaMinus) / (deltaPlus * (1 + deltaPlus) ^ 3) ≤
      2 * (∑ j : Fin κ, delta j ^ 2 / (1 + delta j) ^ 3) /
        (∑ j : Fin κ, delta j / (1 + delta j))
  linfFormula :
    2 * (∑ j : Fin κ, delta j ^ 2 / (1 + delta j) ^ 3) /
        (∑ j : Fin κ, delta j / (1 + delta j)) ≤
      linfNorm

/-- The explicit `L¹` lower bound coming from the radial-window lower bound on each summand. -/
def ComovingDefectFixedRadialWindowNonhidingData.l1LowerBound
    (D : ComovingDefectFixedRadialWindowNonhidingData) : Prop :=
  4 * Real.pi * (D.deltaMinus / (1 + D.deltaPlus)) * D.κ ≤ D.l1Norm

/-- The explicit `L∞` lower bound coming from the exact profile formula and the fixed-window
estimates on numerator and denominator. -/
def ComovingDefectFixedRadialWindowNonhidingData.linfLowerBound
    (D : ComovingDefectFixedRadialWindowNonhidingData) : Prop :=
  2 * D.deltaMinus ^ 2 * (1 + D.deltaMinus) / (D.deltaPlus * (1 + D.deltaPlus) ^ 3) ≤ D.linfNorm

/-- A fixed radial window prevents a nontrivial finite comoving defect profile from hiding: the
exact `L¹` and `L∞` formulas both admit explicit positive lower bounds controlled only by the
window endpoints.
    thm:conclusion-comoving-defect-fixed-radial-window-nonhiding -/
theorem paper_conclusion_comoving_defect_fixed_radial_window_nonhiding
    (D : ComovingDefectFixedRadialWindowNonhidingData) : D.l1LowerBound ∧ D.linfLowerBound := by
  refine ⟨?_, ?_⟩
  · unfold ComovingDefectFixedRadialWindowNonhidingData.l1LowerBound
    rw [D.l1Formula]
    have hsum :
        ∑ _j : Fin D.κ, D.deltaMinus / (1 + D.deltaPlus) ≤
          ∑ j : Fin D.κ, D.delta j / (1 + D.delta j) := by
      exact Finset.sum_le_sum fun j _hj => D.l1SummandLower j
    have hscaled :
        4 * Real.pi * ∑ _j : Fin D.κ, D.deltaMinus / (1 + D.deltaPlus) ≤
          4 * Real.pi * ∑ j : Fin D.κ, D.delta j / (1 + D.delta j) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    calc
      4 * Real.pi * (D.deltaMinus / (1 + D.deltaPlus)) * D.κ
          = 4 * Real.pi * ∑ _j : Fin D.κ, D.deltaMinus / (1 + D.deltaPlus) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ 4 * Real.pi * ∑ j : Fin D.κ, D.delta j / (1 + D.delta j) := hscaled
  · unfold ComovingDefectFixedRadialWindowNonhidingData.linfLowerBound
    exact le_trans D.linfRatioLower D.linfFormula

end Omega.Conclusion
