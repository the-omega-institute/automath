import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Zeta

private lemma xi_time_part9z_window6_escort_projective_identifiability_cross_ratio
    (q : ℝ) :
    let Z6 : ℝ := 8 * Real.rpow 2 q + 4 * Real.rpow 3 q + 9 * Real.rpow 4 q
    let π2 : ℝ := 8 * Real.rpow 2 q / Z6
    let π3 : ℝ := 4 * Real.rpow 3 q / Z6
    let π4 : ℝ := 9 * Real.rpow 4 q / Z6
    9 * π3 ^ 2 / (2 * π2 * π4) = Real.rpow (9 / 8) q := by
  intro Z6 π2 π3 π4
  have hZ : Z6 ≠ 0 := by
    have hZpos : 0 < Z6 := by
      dsimp [Z6]
      positivity
    exact hZpos.ne'
  have h2 : Real.rpow 2 q ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) q).ne'
  have h3 : Real.rpow 3 q ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) q).ne'
  have h4 : Real.rpow 4 q ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) q).ne'
  have h24 : Real.rpow 4 q = Real.rpow 2 q * Real.rpow 2 q := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num]
    change (2 * 2 : ℝ) ^ q = (2 : ℝ) ^ q * (2 : ℝ) ^ q
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2)]
  have h33 : Real.rpow 3 q * Real.rpow 3 q = Real.rpow 9 q := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num]
    change (3 : ℝ) ^ q * (3 : ℝ) ^ q = (3 * 3 : ℝ) ^ q
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 3)]
  have h98 : Real.rpow (9 / 8) q = Real.rpow 9 q / Real.rpow 8 q := by
    change (9 / 8 : ℝ) ^ q = (9 : ℝ) ^ q / (8 : ℝ) ^ q
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 9) (by norm_num : (0 : ℝ) ≤ 8)]
  have h8 : Real.rpow 8 q = Real.rpow 2 q * Real.rpow 4 q := by
    rw [show (8 : ℝ) = 2 * 4 by norm_num]
    change (2 * 4 : ℝ) ^ q = (2 : ℝ) ^ q * (4 : ℝ) ^ q
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 4)]
  dsimp [π2, π3, π4]
  change
    9 * (4 * Real.rpow 3 q / Z6) ^ 2 /
        (2 * (8 * Real.rpow 2 q / Z6) * (9 * Real.rpow 4 q / Z6)) =
      Real.rpow (9 / 8) q
  rw [h98, h8, h24, ← h33]
  field_simp [hZ, h2, h3, h4]
  ring

theorem paper_xi_time_part9z_window6_escort_projective_identifiability (q : ℝ) :
    let Z6 : ℝ := 8 * Real.rpow 2 q + 4 * Real.rpow 3 q + 9 * Real.rpow 4 q
    let π2 : ℝ := 8 * Real.rpow 2 q / Z6
    let π3 : ℝ := 4 * Real.rpow 3 q / Z6
    let π4 : ℝ := 9 * Real.rpow 4 q / Z6
    Real.log (9 * π3 ^ 2 / (2 * π2 * π4)) / Real.log (9 / 8) = q := by
  intro Z6 π2 π3 π4
  have hratio :
      9 * π3 ^ 2 / (2 * π2 * π4) = Real.rpow (9 / 8) q := by
    simpa [Z6, π2, π3, π4]
      using xi_time_part9z_window6_escort_projective_identifiability_cross_ratio q
  have hbase : 0 < (9 / 8 : ℝ) := by norm_num
  have hlog : Real.log (9 / 8 : ℝ) ≠ 0 := by
    have hne : (9 / 8 : ℝ) ≠ 1 := by norm_num
    exact (Real.log_ne_zero_of_pos_of_ne_one hbase hne)
  rw [hratio]
  change Real.log ((9 / 8 : ℝ) ^ q) / Real.log (9 / 8) = q
  rw [Real.log_rpow hbase]
  field_simp [hlog]

end Omega.Zeta
