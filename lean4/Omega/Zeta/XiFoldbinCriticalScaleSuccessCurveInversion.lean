import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinDegeneracyTailCapacityKinks
import Omega.Zeta.XiFoldbinUnderresolutionTwoAtomicCurvatureMeasure

namespace Omega.Zeta

noncomputable section

/-- The continuous critical-scale limiting success curve. -/
def xi_foldbin_critical_scale_success_curve_inversion_success_curve (s : ℝ) : ℝ :=
  if s ≤ Real.goldenRatio⁻¹ then
    Real.goldenRatio ^ 2 / Real.sqrt 5 * s
  else if s ≤ 1 then
    Real.goldenRatio / Real.sqrt 5 * s + (Real.goldenRatio * Real.sqrt 5)⁻¹
  else
    1

/-- The two rigid kink locations of the limiting success curve. -/
def xi_foldbin_critical_scale_success_curve_inversion_kinks : Finset ℝ :=
  {Real.goldenRatio⁻¹, 1}

/-- The closed generalized inverse of the limiting success curve. -/
def xi_foldbin_critical_scale_success_curve_inversion_inverse (α : ℝ) : ℝ :=
  if α ≤ Real.goldenRatio / Real.sqrt 5 then
    Real.sqrt 5 / Real.goldenRatio ^ 2 * α
  else
    (Real.sqrt 5 * α - Real.goldenRatio⁻¹) / Real.goldenRatio

/-- Concrete statement package for the critical-scale success curve and inverse. -/
def xi_foldbin_critical_scale_success_curve_inversion_statement
    (D : Omega.Folding.FoldBinDegeneracyTailCapacityKinksData) : Prop :=
  D.capacityLimit ∧
  (∀ s : ℝ, xi_foldbin_critical_scale_success_curve_inversion_success_curve s =
    if s ≤ Real.goldenRatio⁻¹ then
      Real.goldenRatio ^ 2 / Real.sqrt 5 * s
    else if s ≤ 1 then
      Real.goldenRatio / Real.sqrt 5 * s + (Real.goldenRatio * Real.sqrt 5)⁻¹
    else
      1) ∧
  xi_foldbin_critical_scale_success_curve_inversion_kinks = {Real.goldenRatio⁻¹, 1} ∧
  (∀ α : ℝ, xi_foldbin_critical_scale_success_curve_inversion_inverse α =
    if α ≤ Real.goldenRatio / Real.sqrt 5 then
      Real.sqrt 5 / Real.goldenRatio ^ 2 * α
    else
      (Real.sqrt 5 * α - Real.goldenRatio⁻¹) / Real.goldenRatio) ∧
  xi_foldbin_critical_scale_success_curve_inversion_success_curve 0 = 0 ∧
  xi_foldbin_critical_scale_success_curve_inversion_success_curve 1 = 1

/-- Paper label: `cor:xi-foldbin-critical-scale-success-curve-inversion`. -/
theorem paper_xi_foldbin_critical_scale_success_curve_inversion
    (D : Omega.Folding.FoldBinDegeneracyTailCapacityKinksData) :
    xi_foldbin_critical_scale_success_curve_inversion_statement D := by
  have hcapacity : D.capacityLimit :=
    (Omega.Folding.paper_fold_bin_degeneracy_tail_capacity_kinks D).2
  refine ⟨hcapacity, ?_, rfl, ?_, ?_, ?_⟩
  · intro s
    rfl
  · intro α
    rfl
  · unfold xi_foldbin_critical_scale_success_curve_inversion_success_curve
    rw [if_pos]
    · ring
    · positivity
  · unfold xi_foldbin_critical_scale_success_curve_inversion_success_curve
    rw [if_neg]
    · rw [if_pos le_rfl]
      have hphi_sqrt_ne : Real.goldenRatio * Real.sqrt 5 ≠ 0 := by positivity
      field_simp [hphi_sqrt_ne]
      have hsqrt_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
        norm_num
      nlinarith
    · exact not_le_of_gt (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)

end

end Omega.Zeta
