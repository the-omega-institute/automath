import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic
import Omega.Folding.BinGaugeVolumeStirlingSecondOrder

open scoped BigOperators

namespace Omega.Folding

/-- Logarithmic gauge volume of a finite fiber profile: `log |G_m^bin| = Σ log(d(w)!)`. -/
noncomputable def binGaugeLogVolume {α : Type*} [Fintype α] (d : α → ℕ) : ℝ :=
  ∑ a, Real.log ((Nat.factorial (d a) : ℝ))

/-- The normalized first-order Stirling term `κ_m = 2^{-m} Σ d(w) log d(w)`. -/
noncomputable def binGaugeKappa {α : Type*} [Fintype α] (m : ℕ) (d : α → ℕ) : ℝ :=
  (∑ a, (d a : ℝ) * Real.log (d a)) / (2 : ℝ) ^ m

/-- The normalized logarithmic gauge volume `g_m = 2^{-m} log |G_m^bin|`. -/
noncomputable def binGaugeG {α : Type*} [Fintype α] (m : ℕ) (d : α → ℕ) : ℝ :=
  binGaugeLogVolume d / (2 : ℝ) ^ m

lemma sub_le_log_factorial {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log ((Nat.factorial n : ℝ)) := by
  have hn0 : n ≠ 0 := by omega
  have hlog_nonneg : 0 ≤ Real.log n := by
    exact Real.log_nonneg (by exact_mod_cast hn)
  have hconst_nonneg : 0 ≤ Real.log (2 * Real.pi) / 2 := by
    nlinarith [log_two_pi_ge_eleven_sixths]
  linarith [Stirling.le_log_factorial_stirling (n := n) hn0, hlog_nonneg, hconst_nonneg]

lemma log_factorial_le_mul_log {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((Nat.factorial n : ℝ)) ≤ (n : ℝ) * Real.log n := by
  have hfac_pos : 0 < ((Nat.factorial n : ℝ)) := by
    exact_mod_cast Nat.factorial_pos n
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hfac_le : (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast Nat.factorial_le_pow n
  have hlog_le : Real.log ((Nat.factorial n : ℝ)) ≤ Real.log ((n : ℝ) ^ n) := by
    exact Real.log_le_log hfac_pos hfac_le
  calc
    Real.log ((Nat.factorial n : ℝ)) ≤ Real.log ((n : ℝ) ^ n) := hlog_le
    _ = (n : ℝ) * Real.log n := by
      rw [← Real.rpow_natCast, Real.log_rpow hn_pos]

/-- If the fiber multiplicities sum to `2^m`, then the normalized logarithmic gauge volume lies in
the interval `[κ_m - 1, κ_m]`.
    prop:fold-bin-gauge-volume -/
theorem paper_fold_bin_gauge_volume {α : Type*} [Fintype α]
    (m : ℕ) (d : α → ℕ) (hd : ∀ a, 1 ≤ d a)
    (hsum : ∑ a, d a = 2 ^ m) :
    binGaugeKappa m d - 1 ≤ binGaugeG m d ∧ binGaugeG m d ≤ binGaugeKappa m d := by
  have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
  have hpow_ne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt hpow_pos
  have hsumR : (∑ a, (d a : ℝ)) = (2 : ℝ) ^ m := by
    exact_mod_cast hsum
  have hlower_sum :
      ∑ a, ((d a : ℝ) * Real.log (d a) - (d a : ℝ)) ≤
        ∑ a, Real.log ((Nat.factorial (d a) : ℝ)) := by
    exact Finset.sum_le_sum fun a _ => sub_le_log_factorial (hd a)
  have hlower :
      (∑ a, (d a : ℝ) * Real.log (d a)) ≤
        (∑ a, Real.log ((Nat.factorial (d a) : ℝ))) + (2 : ℝ) ^ m := by
    rw [Finset.sum_sub_distrib, hsumR] at hlower_sum
    linarith
  have hupper :
      (∑ a, Real.log ((Nat.factorial (d a) : ℝ))) ≤
        ∑ a, (d a : ℝ) * Real.log (d a) := by
    exact Finset.sum_le_sum fun a _ => log_factorial_le_mul_log (n := d a) (hd a)
  constructor
  · dsimp [binGaugeKappa, binGaugeG, binGaugeLogVolume]
    field_simp [hpow_ne]
    linarith
  · dsimp [binGaugeKappa, binGaugeG, binGaugeLogVolume]
    field_simp [hpow_ne]
    exact hupper

end Omega.Folding
