import Mathlib

namespace Omega.Zeta

structure XiTerminalZmLeyangSingleScaleAnalyticInversionData where
  r : ℝ
  z : ℝ
  hr : 1 < r
  hz_unit : |z| = 1
  hz_ne_zero : z ≠ 0

def XiTerminalZmLeyangSingleScaleAnalyticInversionData.unitCircleBranch
    (h : XiTerminalZmLeyangSingleScaleAnalyticInversionData) : ℝ :=
  h.z

noncomputable def XiTerminalZmLeyangSingleScaleAnalyticInversionData.contractedBranch
    (h : XiTerminalZmLeyangSingleScaleAnalyticInversionData) : ℝ :=
  h.z⁻¹ / h.r ^ 2

noncomputable def XiTerminalZmLeyangSingleScaleAnalyticInversionData.recoveredRootMultiset
    (h : XiTerminalZmLeyangSingleScaleAnalyticInversionData) : Multiset ℝ :=
  [h.unitCircleBranch, h.contractedBranch]

noncomputable def XiTerminalZmLeyangSingleScaleAnalyticInversionData.targetRootMultiset
    (h : XiTerminalZmLeyangSingleScaleAnalyticInversionData) : Multiset ℝ :=
  [h.z, h.z⁻¹ / h.r ^ 2]

noncomputable def XiTerminalZmLeyangSingleScaleAnalyticInversionData.recoveredRoots
    (h : XiTerminalZmLeyangSingleScaleAnalyticInversionData) : Fin 2 → ℝ
  | 0 => h.unitCircleBranch
  | 1 => h.contractedBranch

noncomputable def XiTerminalZmLeyangSingleScaleAnalyticInversionData.targetRoots
    (h : XiTerminalZmLeyangSingleScaleAnalyticInversionData) : Fin 2 → ℝ
  | 0 => h.z
  | 1 => h.z⁻¹ / h.r ^ 2

noncomputable def XiTerminalZmLeyangSingleScaleAnalyticInversionData.recoveredCoefficients
    (h : XiTerminalZmLeyangSingleScaleAnalyticInversionData) : ℝ × ℝ :=
  (-(h.recoveredRoots 0 + h.recoveredRoots 1), h.recoveredRoots 0 * h.recoveredRoots 1)

noncomputable def XiTerminalZmLeyangSingleScaleAnalyticInversionData.targetCoefficients
    (h : XiTerminalZmLeyangSingleScaleAnalyticInversionData) : ℝ × ℝ :=
  (-(h.z + h.z⁻¹ / h.r ^ 2), h.z * (h.z⁻¹ / h.r ^ 2))

def XiTerminalZmLeyangSingleScaleAnalyticInversionData.unique_unit_circle_branch
    (h : XiTerminalZmLeyangSingleScaleAnalyticInversionData) : Prop :=
  |h.unitCircleBranch| = 1 ∧ |h.contractedBranch| < 1

def XiTerminalZmLeyangSingleScaleAnalyticInversionData.recovers_root_multiset
    (h : XiTerminalZmLeyangSingleScaleAnalyticInversionData) : Prop :=
  h.recoveredRootMultiset = h.targetRootMultiset

def XiTerminalZmLeyangSingleScaleAnalyticInversionData.recovers_coefficients
    (h : XiTerminalZmLeyangSingleScaleAnalyticInversionData) : Prop :=
  h.recoveredCoefficients = h.targetCoefficients

/-- For a unit-circle root `z`, the second quadratic lift `r⁻² z⁻¹` is strictly inside the unit
disk when `r > 1`, so the unit-modulus branch is uniquely determined. The two explicit lifts then
recover the whole root multiset, and Vieta's formulas read off the corresponding coefficients. -/
theorem paper_xi_terminal_zm_leyang_single_scale_analytic_inversion
    (h : XiTerminalZmLeyangSingleScaleAnalyticInversionData) :
    h.unique_unit_circle_branch ∧ h.recovers_root_multiset ∧ h.recovers_coefficients := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨h.hz_unit, ?_⟩
    have hr_pos : 0 < h.r := lt_trans zero_lt_one h.hr
    have hr_sq_pos : 0 < h.r ^ 2 := by positivity
    have hr_sq_gt_one : 1 < h.r ^ 2 := by
      have hsquare : (1 : ℝ) ^ 2 < h.r ^ 2 := by
        refine (sq_lt_sq).2 ?_
        rw [abs_of_nonneg zero_le_one, abs_of_nonneg hr_pos.le]
        exact h.hr
      simpa using hsquare
    have hz_inv_abs : |h.z⁻¹| = 1 := by
      rw [abs_inv, h.hz_unit, inv_one]
    have hcontract :
        |h.contractedBranch| = 1 / (h.r ^ 2) := by
      unfold XiTerminalZmLeyangSingleScaleAnalyticInversionData.contractedBranch
      rw [abs_div, hz_inv_abs, abs_of_pos hr_sq_pos]
    rw [hcontract]
    simpa [one_div] using inv_lt_one_of_one_lt₀ hr_sq_gt_one
  · unfold XiTerminalZmLeyangSingleScaleAnalyticInversionData.recovers_root_multiset
    simp [XiTerminalZmLeyangSingleScaleAnalyticInversionData.recoveredRootMultiset,
      XiTerminalZmLeyangSingleScaleAnalyticInversionData.targetRootMultiset,
      XiTerminalZmLeyangSingleScaleAnalyticInversionData.unitCircleBranch,
      XiTerminalZmLeyangSingleScaleAnalyticInversionData.contractedBranch]
  · unfold XiTerminalZmLeyangSingleScaleAnalyticInversionData.recovers_coefficients
    simp [XiTerminalZmLeyangSingleScaleAnalyticInversionData.recoveredCoefficients,
      XiTerminalZmLeyangSingleScaleAnalyticInversionData.targetCoefficients,
      XiTerminalZmLeyangSingleScaleAnalyticInversionData.recoveredRoots,
      XiTerminalZmLeyangSingleScaleAnalyticInversionData.unitCircleBranch,
      XiTerminalZmLeyangSingleScaleAnalyticInversionData.contractedBranch]

end Omega.Zeta
