import Omega.UnitCirclePhaseArithmetic.ComovingBitBudget
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The compactified comoving coordinate used for the radial readout. -/
def unit_circle_comoving_radial_bit_complexity_compactified (x : ℝ) : ℝ :=
  Real.arctan x / Real.pi

/-- First-order local readout budget for recovering the uncompactified radial coordinate from an
error `Δu` in the compactified coordinate. -/
def unit_circle_comoving_radial_bit_complexity_local_readout_error (x Δu : ℝ) : ℝ :=
  Real.pi * (1 + x ^ 2) * |Δu|

/-- Dyadic threshold for resolving the compactified radial coordinate to absolute readout error
`ε` in the original coordinate. -/
noncomputable def unit_circle_comoving_radial_bit_complexity_required_bits
    (x ε : ℝ) : ℝ :=
  Real.logb 2 (Real.pi * (1 + x ^ 2) / ε)

/-- Concrete bit-complexity package for the compactified radial readout. -/
def unit_circle_comoving_radial_bit_complexity_statement : Prop :=
  ∀ x ε n : ℝ,
    0 < ε →
    (2 : ℝ) ^ (-n) ≤ ε / (Real.pi * (1 + x ^ 2)) →
      deriv unit_circle_comoving_radial_bit_complexity_compactified x =
          1 / (Real.pi * (1 + x ^ 2)) ∧
        unit_circle_comoving_radial_bit_complexity_compactified x = Real.arctan x / Real.pi ∧
        unit_circle_comoving_radial_bit_complexity_local_readout_error x ((2 : ℝ) ^ (-n)) ≤ ε ∧
        unit_circle_comoving_radial_bit_complexity_required_bits x ε =
          Real.logb 2 (1 / ε) + Real.logb 2 (1 + x ^ 2) + Real.logb 2 Real.pi ∧
        unit_circle_comoving_radial_bit_complexity_required_bits x ε ≤ n

lemma unit_circle_comoving_radial_bit_complexity_compactified_deriv (x : ℝ) :
    deriv unit_circle_comoving_radial_bit_complexity_compactified x =
      1 / (Real.pi * (1 + x ^ 2)) := by
  have hx_pos : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hderiv :
      HasDerivAt (fun t : ℝ => (1 / Real.pi) * Real.arctan t)
        ((1 / Real.pi) * (1 / (1 + x ^ 2))) x :=
    (Real.hasDerivAt_arctan x).const_mul (1 / Real.pi)
  calc
    deriv unit_circle_comoving_radial_bit_complexity_compactified x =
        (1 / Real.pi) * (1 / (1 + x ^ 2)) := by
          unfold unit_circle_comoving_radial_bit_complexity_compactified
          simpa [div_eq_mul_inv, mul_comm] using hderiv.deriv
    _ = 1 / (Real.pi * (1 + x ^ 2)) := by
          field_simp [Real.pi_ne_zero, ne_of_gt hx_pos]

lemma unit_circle_comoving_radial_bit_complexity_required_bits_expand
    {x ε : ℝ} (hε : 0 < ε) :
    unit_circle_comoving_radial_bit_complexity_required_bits x ε =
      Real.logb 2 (1 / ε) + Real.logb 2 (1 + x ^ 2) + Real.logb 2 Real.pi := by
  have hpi_ne : Real.pi ≠ 0 := by exact Real.pi_ne_zero
  have hx_ne : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  have hmul_ne : Real.pi * (1 + x ^ 2) ≠ 0 := mul_ne_zero hpi_ne hx_ne
  rw [unit_circle_comoving_radial_bit_complexity_required_bits,
    Real.logb_div hmul_ne (ne_of_gt hε), Real.logb_mul hpi_ne hx_ne]
  simp [sub_eq_add_neg, Real.logb_inv]
  ring

/-- Paper label: `prop:unit-circle-comoving-radial-bit-complexity`. The compactified coordinate
`u = arctan(x) / π` has derivative `1 / (π (1 + x²))`, so a dyadic `u`-resolution below
`ε / (π (1 + x²))` yields readout error at most `ε` in the original coordinate and forces the
advertised base-2 threshold. -/
theorem paper_unit_circle_comoving_radial_bit_complexity :
    unit_circle_comoving_radial_bit_complexity_statement := by
  intro x ε n hε hres
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hx_pos : 0 < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  let unit_circle_comoving_radial_bit_complexity_budget_arg : ℝ := Real.pi * (1 + x ^ 2) / ε
  have harg_pos : 0 < unit_circle_comoving_radial_bit_complexity_budget_arg := by
    dsimp [unit_circle_comoving_radial_bit_complexity_budget_arg]
    positivity
  have hpow_pos : 0 < (2 : ℝ) ^ n := by
    exact Real.rpow_pos_of_pos (by norm_num) n
  have hbudget_le_pow : unit_circle_comoving_radial_bit_complexity_budget_arg ≤ (2 : ℝ) ^ n := by
    have hmul := mul_le_mul_of_nonneg_left hres harg_pos.le
    have hpow_neg : (2 : ℝ) ^ (-n) = ((2 : ℝ) ^ n)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    have hunit :
        unit_circle_comoving_radial_bit_complexity_budget_arg *
            (ε / (Real.pi * (1 + x ^ 2))) =
          1 := by
      dsimp [unit_circle_comoving_radial_bit_complexity_budget_arg]
      field_simp [ne_of_gt hε, Real.pi_ne_zero, ne_of_gt hx_pos]
    have htmp :
        unit_circle_comoving_radial_bit_complexity_budget_arg * (2 : ℝ) ^ (-n) ≤ 1 := by
      calc
        unit_circle_comoving_radial_bit_complexity_budget_arg * (2 : ℝ) ^ (-n) ≤
            unit_circle_comoving_radial_bit_complexity_budget_arg *
              (ε / (Real.pi * (1 + x ^ 2))) := hmul
        _ = 1 := hunit
    have hdiv : unit_circle_comoving_radial_bit_complexity_budget_arg / (2 : ℝ) ^ n ≤ 1 := by
      simpa [unit_circle_comoving_radial_bit_complexity_budget_arg, div_eq_mul_inv, hpow_neg,
        mul_assoc, mul_left_comm, mul_comm] using htmp
    simpa using (div_le_iff₀ hpow_pos).1 hdiv
  have hbudget_log :
      unit_circle_comoving_radial_bit_complexity_required_bits x ε ≤ n := by
    dsimp [unit_circle_comoving_radial_bit_complexity_required_bits,
      unit_circle_comoving_radial_bit_complexity_budget_arg]
    have hlog :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) harg_pos hbudget_le_pow
    simpa [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] using hlog
  have hstep_nonneg : 0 ≤ (2 : ℝ) ^ (-n) := by positivity
  have hreadout :
      unit_circle_comoving_radial_bit_complexity_local_readout_error x ((2 : ℝ) ^ (-n)) ≤ ε := by
    have hmain :
        Real.pi * (1 + x ^ 2) * |(2 : ℝ) ^ (-n)| ≤
          Real.pi * (1 + x ^ 2) * (ε / (Real.pi * (1 + x ^ 2))) := by
      exact mul_le_mul_of_nonneg_left (by simpa [abs_of_nonneg hstep_nonneg] using hres)
        (by positivity)
    have hright : Real.pi * (1 + x ^ 2) * (ε / (Real.pi * (1 + x ^ 2))) = ε := by
      field_simp [Real.pi_ne_zero, ne_of_gt hx_pos]
    calc
      unit_circle_comoving_radial_bit_complexity_local_readout_error x ((2 : ℝ) ^ (-n)) =
          Real.pi * (1 + x ^ 2) * |(2 : ℝ) ^ (-n)| := by
            rfl
      _ ≤ Real.pi * (1 + x ^ 2) * (ε / (Real.pi * (1 + x ^ 2))) := hmain
      _ = ε := hright
  refine ⟨unit_circle_comoving_radial_bit_complexity_compactified_deriv x, rfl, hreadout, ?_, ?_⟩
  · exact unit_circle_comoving_radial_bit_complexity_required_bits_expand hε
  · exact hbudget_log

end

end Omega.UnitCirclePhaseArithmetic
