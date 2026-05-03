import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

theorem paper_xi_kappakl_ar_closed_asymptotic (kappaKL : ℝ → ℝ)
    (hkappa : ∀ a, a ≠ 1 → kappaKL a = (a - 1 - Real.log a) / (a - 1) ^ 2)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    kappaKL ((1 - r) / (1 + r)) =
      ((1 + r) ^ 2 / (4 * r ^ 2)) * Real.log ((1 + r) / (1 - r)) -
        (1 + r) / (2 * r) := by
  have hr_ne : r ≠ 0 := ne_of_gt hr0
  have h1pr_ne : 1 + r ≠ 0 := by nlinarith
  have h1mr_ne : 1 - r ≠ 0 := by nlinarith
  have ha_ne : (1 - r) / (1 + r) ≠ 1 := by
    intro h
    have : 1 - r = 1 + r := by
      calc
        1 - r = ((1 - r) / (1 + r)) * (1 + r) := by field_simp [h1pr_ne]
        _ = 1 + r := by rw [h, one_mul]
    nlinarith
  have hlog :
      Real.log ((1 - r) / (1 + r)) = -Real.log ((1 + r) / (1 - r)) := by
    calc
      Real.log ((1 - r) / (1 + r)) =
          Real.log (((1 + r) / (1 - r))⁻¹) := by
        congr 1
        field_simp [h1pr_ne, h1mr_ne]
      _ = -Real.log ((1 + r) / (1 - r)) := by rw [Real.log_inv]
  have ha_sub : (1 - r) / (1 + r) - 1 = -(2 * r) / (1 + r) := by
    field_simp [h1pr_ne]
    ring
  rw [hkappa _ ha_ne, hlog, ha_sub]
  field_simp [hr_ne, h1pr_ne]
  ring_nf
