import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

namespace Omega.Zeta

/-- The compactified height coordinate used in the paper. -/
noncomputable def xi_compactified_dyadic_depth_lower_bound_u (t : ℝ) : ℝ :=
  Real.arctan t / Real.pi

/-- The model upper bound for the compactified gap size. -/
noncomputable def xi_compactified_dyadic_depth_lower_bound_gap_bound_value (T : ℝ) : ℝ :=
  2 / ((1 + T ^ 2) * Real.log (T / (2 * Real.pi)))

/-- Positivity of the compactified gap bound at height `T`. -/
def xi_compactified_dyadic_depth_lower_bound_compactified_gap_bound (T : ℝ) : Prop :=
  0 < xi_compactified_dyadic_depth_lower_bound_gap_bound_value T

/-- The dyadic bit-depth lower bound forced by the gap estimate at height `T`. -/
def xi_compactified_dyadic_depth_lower_bound_dyadic_bitdepth_lower_bound (T b : ℝ) : Prop :=
  Real.logb 2 ((1 + T ^ 2) * Real.log (T / (2 * Real.pi))) - 1 ≤ b

private lemma xi_compactified_dyadic_depth_lower_bound_scale_pos {T : ℝ}
    (hT : 2 * Real.pi < T) : 0 < ((1 + T ^ 2) * Real.log (T / (2 * Real.pi))) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hratio : 1 < T / (2 * Real.pi) := by
    rw [one_lt_div hpi]
    linarith
  have hlog : 0 < Real.log (T / (2 * Real.pi)) := Real.log_pos hratio
  positivity

/-- Paper label: `thm:xi-compactified-dyadic-depth-lower-bound`. -/
theorem paper_xi_compactified_dyadic_depth_lower_bound (T b : ℝ) (hT : 2 * Real.pi < T)
    (hb : (2 : ℝ) ^ (-b) ≤ xi_compactified_dyadic_depth_lower_bound_gap_bound_value T) :
    xi_compactified_dyadic_depth_lower_bound_compactified_gap_bound T ∧
      xi_compactified_dyadic_depth_lower_bound_dyadic_bitdepth_lower_bound T b := by
  let A : ℝ := (1 + T ^ 2) * Real.log (T / (2 * Real.pi))
  have hApos : 0 < A := by
    dsimp [A]
    exact xi_compactified_dyadic_depth_lower_bound_scale_pos hT
  have hgap_pos : 0 < xi_compactified_dyadic_depth_lower_bound_gap_bound_value T := by
    unfold xi_compactified_dyadic_depth_lower_bound_gap_bound_value
    positivity
  have hmul : A * (2 : ℝ) ^ (-b) ≤ 2 := by
    calc
      A * (2 : ℝ) ^ (-b) ≤ A * (2 / A) := by
        simpa [A, xi_compactified_dyadic_depth_lower_bound_gap_bound_value]
          using mul_le_mul_of_nonneg_left hb hApos.le
      _ = 2 := by
        field_simp [hApos.ne']
  have hpow_pos : 0 < (2 : ℝ) ^ b := Real.rpow_pos_of_pos (by norm_num) b
  have hcancel : (2 : ℝ) ^ (-b) * (2 : ℝ) ^ b = 1 := by
    rw [← Real.rpow_add (by positivity)]
    simp
  have hA_le_pow : A ≤ (2 : ℝ) ^ (b + 1) := by
    have hmul' := mul_le_mul_of_nonneg_right hmul hpow_pos.le
    calc
      A = (A * (2 : ℝ) ^ (-b)) * (2 : ℝ) ^ b := by
        rw [mul_assoc, hcancel, mul_one]
      _ ≤ 2 * (2 : ℝ) ^ b := hmul'
      _ = (2 : ℝ) ^ (b + 1) := by
        calc
          2 * (2 : ℝ) ^ b = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ b := by norm_num
          _ = (2 : ℝ) ^ (1 + b) := by rw [← Real.rpow_add (by positivity)]
          _ = (2 : ℝ) ^ (b + 1) := by ring_nf
  have hlog : Real.logb 2 A ≤ b + 1 := by
    calc
      Real.logb 2 A ≤ Real.logb 2 ((2 : ℝ) ^ (b + 1)) := by
        exact Real.logb_le_logb_of_le (by norm_num) hApos hA_le_pow
      _ = b + 1 := by
        rw [Real.logb_rpow (by norm_num) (by norm_num : (2 : ℝ) ≠ 1)]
  refine ⟨hgap_pos, ?_⟩
  unfold xi_compactified_dyadic_depth_lower_bound_dyadic_bitdepth_lower_bound
  have hdepth : Real.logb 2 A - 1 ≤ b := by
    linarith
  simpa [A] using hdepth

end Omega.Zeta
