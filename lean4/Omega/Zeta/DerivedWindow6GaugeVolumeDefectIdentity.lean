import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.GaugeGroupTripleDecomp

namespace Omega.Zeta

/-- The exact window-`6` bin-gauge group order coming from the `S₂^8 × S₃^4 × S₄^9`
decomposition. -/
def window6GaugeGroupOrder : ℕ :=
  Nat.factorial 2 ^ 8 * Nat.factorial 3 ^ 4 * Nat.factorial 4 ^ 9

/-- The normalized logarithmic gauge density `g₆ = (1 / 64) log |G₆^{bin}|`. -/
noncomputable def window6GaugeLogDensity : ℝ :=
  Real.log (window6GaugeGroupOrder : ℝ) / 64

/-- The normalized gauge-volume density `κ₆` from the histogram `2:8, 3:4, 4:9`. -/
noncomputable def window6GaugeVolumeDensity : ℝ :=
  (8 * (2 : ℝ) * Real.log 2 + 4 * (3 : ℝ) * Real.log 3 + 9 * (4 : ℝ) * Real.log 4) / 64

private lemma real_log_pow_nat (x : ℝ) (n : ℕ) (hx : 0 < x) :
    Real.log (x ^ n) = (n : ℝ) * Real.log x := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        Real.log (x ^ (n + 1)) = Real.log (x ^ n * x) := by
              simp [pow_succ', mul_comm]
        _ = Real.log (x ^ n) + Real.log x := by
              rw [Real.log_mul (pow_ne_zero _ hx.ne') (show x ≠ 0 by positivity)]
        _ = (n : ℝ) * Real.log x + Real.log x := by rw [ih]
        _ = ((n + 1 : ℕ) : ℝ) * Real.log x := by
              rw [Nat.cast_add, Nat.cast_one]
              ring

private lemma window6GaugeGroupOrder_closed :
    window6GaugeGroupOrder = 2 ^ 39 * 3 ^ 13 := by
  have hfac := GaugeGroupTripleDecomp.gauge_group_factor_orders
  have h2 : Nat.factorial 2 = 2 := hfac.1
  have h3 : Nat.factorial 3 = 6 := hfac.2.1
  have h4 : Nat.factorial 4 = 24 := hfac.2.2
  rw [window6GaugeGroupOrder, h2, h3, h4]
  norm_num [pow_add, pow_mul]

private lemma window6GaugeLogDensity_closed :
    window6GaugeLogDensity = (39 * Real.log 2 + 13 * Real.log 3) / 64 := by
  have horder :
      (window6GaugeGroupOrder : ℝ) = (2 : ℝ) ^ 39 * (3 : ℝ) ^ 13 := by
    norm_num [window6GaugeGroupOrder_closed]
  rw [window6GaugeLogDensity, horder, Real.log_mul (by positivity) (by positivity)]
  rw [real_log_pow_nat 2 39 (by positivity), real_log_pow_nat 3 13 (by positivity)]
  ring

private lemma window6GaugeVolumeDensity_closed :
    window6GaugeVolumeDensity = (88 * Real.log 2 + 12 * Real.log 3) / 64 := by
  rw [window6GaugeVolumeDensity]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, real_log_pow_nat 2 2 (by positivity)]
    norm_num
  rw [hlog4]
  ring

/-- Paper label: `thm:derived-window6-gauge-volume-defect-identity`. The window-`6`
group-order normalization and the histogram computation give the exact gauge-volume density,
log-density, defect gap, and exponential ratio. -/
theorem paper_derived_window6_gauge_volume_defect_identity :
    window6GaugeGroupOrder = 2 ^ 39 * 3 ^ 13 ∧
      window6GaugeLogDensity = (39 * Real.log 2 + 13 * Real.log 3) / 64 ∧
      window6GaugeVolumeDensity = (88 * Real.log 2 + 12 * Real.log 3) / 64 ∧
      window6GaugeVolumeDensity - window6GaugeLogDensity = (49 * Real.log 2 - Real.log 3) / 64 ∧
      Real.exp (64 * window6GaugeVolumeDensity) / (window6GaugeGroupOrder : ℝ) =
        (2 : ℝ) ^ 49 / 3 := by
  refine ⟨window6GaugeGroupOrder_closed, window6GaugeLogDensity_closed,
    window6GaugeVolumeDensity_closed, ?_, ?_⟩
  · rw [window6GaugeVolumeDensity_closed, window6GaugeLogDensity_closed]
    ring
  · rw [window6GaugeVolumeDensity_closed, window6GaugeGroupOrder_closed]
    have hlog4 : 64 * ((88 * Real.log 2 + 12 * Real.log 3) / 64) = 88 * Real.log 2 + 12 * Real.log 3 := by
      ring
    rw [hlog4, Real.exp_add]
    rw [show 88 * Real.log 2 = Real.log ((2 : ℝ) ^ 88) by
      symm
      exact real_log_pow_nat 2 88 (by positivity)]
    rw [show 12 * Real.log 3 = Real.log ((3 : ℝ) ^ 12) by
      symm
      exact real_log_pow_nat 3 12 (by positivity)]
    rw [Real.exp_log (by positivity), Real.exp_log (by positivity)]
    field_simp
    ring_nf

end Omega.Zeta
