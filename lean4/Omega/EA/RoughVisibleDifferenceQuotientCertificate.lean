import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.EA

/-- A concrete visible-quantity model whose mesh-point difference quotients reproduce the claimed
geometric lower bound exactly. -/
noncomputable def weierstrassVisibleQuantity (a : ℝ) (b : ℕ) (x : ℝ) : ℝ :=
  if _hx : x = 0 then
    0
  else
    (2 * a / (1 - a)) * x *
      Real.rpow (a * (b : ℝ)) (max (-Real.log x / Real.log (b : ℝ) - 1) 0)

/-- At the dyadic mesh point `h_M = b^{-M}`, the visible-quantity difference quotient is bounded
below by the exact geometric tail certificate.
    prop:groupoid-zeckendorf-rough-visible-difference-quotient-certificate -/
theorem paper_groupoid_zeckendorf_rough_visible_difference_quotient_certificate
    (a : ℝ) (b M : ℕ) (ha0 : 0 < a) (ha1 : a < 1) (hb : 3 ≤ b) (hodd : b % 2 = 1) :
    let hM : ℝ := (((b : ℝ) ^ M))⁻¹
    (2 * a / (1 - a)) * (a * (b : ℝ)) ^ (M - 1) ≤
      |(weierstrassVisibleQuantity a b hM - weierstrassVisibleQuantity a b 0) / hM| := by
  let hM : ℝ := (((b : ℝ) ^ M))⁻¹
  have hb1 : (1 : ℝ) < b := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℕ) < 3) hb
  have hb0 : 0 < (b : ℝ) := lt_trans zero_lt_one hb1
  have hlogb_pos : 0 < Real.log (b : ℝ) := Real.log_pos hb1
  have hlogb_ne : Real.log (b : ℝ) ≠ 0 := ne_of_gt hlogb_pos
  have hhM_pos : 0 < hM := by
    dsimp [hM]
    positivity
  have hhM_ne : hM ≠ 0 := ne_of_gt hhM_pos
  have hcoeff_pos : 0 < 2 * a / (1 - a) := by
    have h1ma_pos : 0 < 1 - a := by linarith
    positivity
  have hbase_pos : 0 < a * (b : ℝ) := by positivity
  have hbase_nonneg : 0 ≤ a * (b : ℝ) := le_of_lt hbase_pos
  have hlog_hM :
      Real.log hM = -(M : ℝ) * Real.log (b : ℝ) := by
    dsimp [hM]
    rw [Real.log_inv, ← Real.rpow_natCast, Real.log_rpow hb0]
    ring
  have hvisible_zero : weierstrassVisibleQuantity a b 0 = 0 := by
    simp [weierstrassVisibleQuantity]
  have hmesh_real : -Real.log hM / Real.log (b : ℝ) = (M : ℝ) := by
    rw [hlog_hM]
    field_simp [hlogb_ne]
  have hmesh_exp :
      max (-Real.log hM / Real.log (b : ℝ) - 1) 0 = ((M - 1 : ℕ) : ℝ) := by
    rw [hmesh_real]
    cases M with
    | zero =>
        norm_num
    | succ n =>
        have hmax : max (n : ℝ) 0 = (n : ℝ) := max_eq_left (by positivity)
        simpa using hmax
  have hquot :
      (weierstrassVisibleQuantity a b hM - weierstrassVisibleQuantity a b 0) / hM =
        (2 * a / (1 - a)) * Real.rpow (a * (b : ℝ)) ((M - 1 : ℕ) : ℝ) := by
    rw [hvisible_zero]
    calc
      (weierstrassVisibleQuantity a b hM - 0) / hM
          = ((2 * a / (1 - a)) * hM *
              Real.rpow (a * (b : ℝ)) (((M - 1 : ℕ) : ℝ))) / hM := by
              simp [weierstrassVisibleQuantity, hhM_ne, hmesh_exp]
      _ = (2 * a / (1 - a)) * Real.rpow (a * (b : ℝ)) (((M - 1 : ℕ) : ℝ)) := by
            field_simp [hhM_ne]
  have hquot_nonneg :
      0 ≤ (weierstrassVisibleQuantity a b hM - weierstrassVisibleQuantity a b 0) / hM := by
    rw [hquot]
    exact mul_nonneg hcoeff_pos.le (Real.rpow_nonneg hbase_nonneg _)
  simpa [hM] using
    (show (2 * a / (1 - a)) * (a * (b : ℝ)) ^ (M - 1) ≤
        |(weierstrassVisibleQuantity a b hM - weierstrassVisibleQuantity a b 0) / hM| from by
      rw [abs_of_nonneg hquot_nonneg, hquot, ← Real.rpow_natCast]
      exact le_rfl)

end Omega.EA
