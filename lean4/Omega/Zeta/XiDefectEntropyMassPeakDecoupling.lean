import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiDefectEntropyPeakCompressibilityExtremal

namespace Omega.Zeta

/-- Paper label: `cor:xi-defect-entropy-mass-peak-decoupling`. -/
theorem paper_xi_defect_entropy_mass_peak_decoupling
    (κ : ℕ) (S : ℝ) (hκ : 0 < κ) (hS0 : 0 < S) (hSκ : S < κ) :
    xiPeakCompressibility κ S ≤ 8 / (κ + 1 : ℝ) := by
  let M := xiDefectFloor S
  let r := xiDefectFraction S
  let a := xiDefectAStar κ S
  have hformula :
      xiPeakCompressibility κ S = 4 * a * (1 - a) := by
    simpa [a] using
      (paper_xi_defect_entropy_peak_compressibility_extremal κ S hκ hS0 hSκ).1
  have hMltκ : M < κ := by
    dsimp [M, xiDefectFloor]
    exact (Nat.floor_lt hS0.le).2 hSκ
  have hrlt : r < 1 := by
    dsimp [r, xiDefectFraction, xiDefectFloor]
    have h := Nat.lt_floor_add_one S
    linarith
  have hrnonneg : 0 ≤ r := by
    dsimp [r, xiDefectFraction, xiDefectFloor]
    exact sub_nonneg.mpr (Nat.floor_le hS0.le)
  have hApos : 0 < (κ - M : ℝ) := by
    have hMk : (M : ℝ) < κ := by
      exact_mod_cast hMltκ
    linarith
  have hBpos : 0 < (M + 1 : ℝ) := by
    positivity
  have hA :
      a ≤ 1 / (κ - M : ℝ) := by
    have hfrac :
        r / (κ - M : ℝ) ≤ 1 / (κ - M : ℝ) := by
      exact div_le_div_of_nonneg_right (le_of_lt hrlt) hApos.le
    have hmin :
        a ≤ r / (κ - M : ℝ) := by
      dsimp [a, xiDefectAStar, M, r]
      exact min_le_left _ _
    exact hmin.trans hfrac
  have hB :
      a ≤ 1 / (M + 1 : ℝ) := by
    have hfrac :
        (1 - r) / (M + 1 : ℝ) ≤ 1 / (M + 1 : ℝ) := by
      have hnum : 1 - r ≤ 1 := by linarith
      exact div_le_div_of_nonneg_right hnum hBpos.le
    have hmin :
        a ≤ (1 - r) / (M + 1 : ℝ) := by
      dsimp [a, xiDefectAStar, M, r]
      exact min_le_right _ _
    exact hmin.trans hfrac
  have ha_nonneg : 0 ≤ a := by
    dsimp [a, xiDefectAStar, M, r]
    refine le_min ?_ ?_
    · exact div_nonneg hrnonneg hApos.le
    · have : 0 ≤ 1 - r := by linarith
      exact div_nonneg this hBpos.le
  have hsum : (κ - M : ℝ) + (M + 1 : ℝ) = κ + 1 := by
    ring
  have hmin_bound : min (1 / (κ - M : ℝ)) (1 / (M + 1 : ℝ)) ≤ 2 / (κ + 1 : ℝ) := by
    rcases le_total (κ - M : ℝ) (M + 1 : ℝ) with hAB | hBA
    · calc
        min (1 / (κ - M : ℝ)) (1 / (M + 1 : ℝ)) ≤ 1 / (M + 1 : ℝ) := min_le_right _ _
        _ ≤ 1 / (((κ - M : ℝ) + (M + 1 : ℝ)) / 2) := by
          have hhalf_pos : 0 < (((κ - M : ℝ) + (M + 1 : ℝ)) / 2) := by positivity
          have hhalf_le : (((κ - M : ℝ) + (M + 1 : ℝ)) / 2) ≤ (M + 1 : ℝ) := by
            linarith
          exact one_div_le_one_div_of_le hhalf_pos hhalf_le
        _ = 2 / (κ + 1 : ℝ) := by
          rw [hsum]
          field_simp
    · calc
        min (1 / (κ - M : ℝ)) (1 / (M + 1 : ℝ)) ≤ 1 / (κ - M : ℝ) := min_le_left _ _
        _ ≤ 1 / (((κ - M : ℝ) + (M + 1 : ℝ)) / 2) := by
          have hhalf_pos : 0 < (((κ - M : ℝ) + (M + 1 : ℝ)) / 2) := by positivity
          have hhalf_le : (((κ - M : ℝ) + (M + 1 : ℝ)) / 2) ≤ (κ - M : ℝ) := by
            linarith
          exact one_div_le_one_div_of_le hhalf_pos hhalf_le
        _ = 2 / (κ + 1 : ℝ) := by
          rw [hsum]
          field_simp
  have ha_bound : a ≤ 2 / (κ + 1 : ℝ) := by
    exact (le_min hA hB).trans hmin_bound
  have htwo_bound : 2 / (κ + 1 : ℝ) ≤ 1 := by
    have hden : (2 : ℝ) ≤ κ + 1 := by
      have hkreal : (1 : ℝ) ≤ κ := by
        exact_mod_cast hκ
      nlinarith
    have hrecip : 1 / (κ + 1 : ℝ) ≤ 1 / 2 := by
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden
    have hmul := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 2)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have ha_le_one : a ≤ 1 := ha_bound.trans htwo_bound
  calc
    xiPeakCompressibility κ S = 4 * a * (1 - a) := hformula
    _ ≤ 4 * a := by nlinarith
    _ ≤ 4 * (2 / (κ + 1 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left ha_bound (by norm_num)
    _ = 8 / (κ + 1 : ℝ) := by ring
