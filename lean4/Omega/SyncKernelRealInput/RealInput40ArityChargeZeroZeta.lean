import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40ArityChargeDetClosed

namespace Omega.SyncKernelRealInput

open Omega.SyncKernelWeighted

/-- The zero-charge denominator obtained from the `q = 0` specialization of the audited
arity-charge determinant. -/
def real_input_40_arity_charge_zero_zeta_den (z : ℚ) : ℚ :=
  (1 - z ^ 2) * (1 - z - z ^ 4)

/-- The zero-charge dynamical zeta function. -/
def real_input_40_arity_charge_zero_zeta (z : ℚ) : ℚ :=
  (real_input_40_arity_charge_zero_zeta_den z)⁻¹

/-- The Perron quartic controlling the dominant real singularity of the zero-charge zeta factor. -/
def real_input_40_arity_charge_zero_zeta_quartic (κ : ℝ) : ℝ :=
  κ ^ 4 - κ ^ 3 - 1

private lemma real_input_40_arity_charge_zero_zeta_det_q0
    (z : ℚ) :
    real_input_40_arity_charge_det_closed_det z 0 =
      real_input_40_arity_charge_zero_zeta_den z := by
  simp [real_input_40_arity_charge_zero_zeta_den, real_input_40_arity_charge_det_closed_det,
    real_input_40_arity_charge_det_closed_Q7]
  ring

private lemma real_input_40_arity_charge_zero_zeta_quartic_continuous :
    Continuous real_input_40_arity_charge_zero_zeta_quartic := by
  simpa [real_input_40_arity_charge_zero_zeta_quartic] using
    ((continuous_id.pow 4).sub (continuous_id.pow 3)).sub continuous_const

private lemma real_input_40_arity_charge_zero_zeta_quartic_strictMonoOn :
    StrictMonoOn real_input_40_arity_charge_zero_zeta_quartic (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx1 : 1 ≤ x := hx
  have hy1 : 1 ≤ y := hy
  have hxy_pos : 0 < y - x := sub_pos.mpr hxy
  have hfactor :
      real_input_40_arity_charge_zero_zeta_quartic y -
          real_input_40_arity_charge_zero_zeta_quartic x =
        (y - x) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - (x ^ 2 + x * y + y ^ 2)) := by
    unfold real_input_40_arity_charge_zero_zeta_quartic
    ring
  have hbracket : 0 < x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - (x ^ 2 + x * y + y ^ 2) := by
    have hx_sq_le_cu : x ^ 2 ≤ x ^ 3 := by
      nlinarith
    have hxy_le : x * y ≤ x ^ 2 * y := by
      nlinarith
    have hy_sq_le : y ^ 2 ≤ x * y ^ 2 := by
      nlinarith
    have hy_cu_pos : 0 < y ^ 3 := by
      positivity
    nlinarith
  have hpos :
      0 <
        real_input_40_arity_charge_zero_zeta_quartic y -
          real_input_40_arity_charge_zero_zeta_quartic x := by
    rw [hfactor]
    exact mul_pos hxy_pos hbracket
  linarith

/-- Paper label: `prop:real-input-40-arity-charge-zero-zeta`. The zero-charge specialization of
the real-input-`40` arity-charge determinant is the rational factor
`((1 - z²) (1 - z - z⁴))⁻¹`, and the dominant real growth parameter is the unique root of
`κ⁴ - κ³ - 1` in `(1, 2)`. -/
theorem paper_real_input_40_arity_charge_zero_zeta :
    (∀ z : ℚ,
      real_input_40_arity_charge_zero_zeta z =
        (real_input_40_arity_charge_det_closed_det z 0)⁻¹) ∧
      (∀ z : ℚ,
        real_input_40_arity_charge_zero_zeta z = ((1 - z ^ 2) * (1 - z - z ^ 4))⁻¹) ∧
      ∃! κ : ℝ, κ ∈ Set.Ioo 1 2 ∧ real_input_40_arity_charge_zero_zeta_quartic κ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    rw [real_input_40_arity_charge_zero_zeta_det_q0 z]
    rfl
  · intro z
    rfl
  · have hzero_mem :
        (0 : ℝ) ∈
          Set.Ioo (real_input_40_arity_charge_zero_zeta_quartic 1)
            (real_input_40_arity_charge_zero_zeta_quartic 2) := by
      norm_num [real_input_40_arity_charge_zero_zeta_quartic]
    rcases intermediate_value_Ioo (show (1 : ℝ) ≤ 2 by norm_num)
        real_input_40_arity_charge_zero_zeta_quartic_continuous.continuousOn hzero_mem with
      ⟨κ, hκIoo, hκroot⟩
    refine ⟨κ, ⟨hκIoo, hκroot⟩, ?_⟩
    intro κ' hκ'
    rcases hκ' with ⟨hκ'Ioo, hκ'root⟩
    exact
      (real_input_40_arity_charge_zero_zeta_quartic_strictMonoOn.injOn
        (show κ ∈ Set.Ici 1 from le_of_lt hκIoo.1)
        (show κ' ∈ Set.Ici 1 from le_of_lt hκ'Ioo.1)
        (by simp [hκroot, hκ'root])).symm

end Omega.SyncKernelRealInput
