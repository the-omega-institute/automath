import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic

open Filter
open scoped Asymptotics Topology

namespace Omega.Zeta

lemma xi_time_part69_localized_rational_endomorphism_growth_rate_pow_gap_cast_of_lt
    {a b m : ℕ} (hab : a < b) :
    ((Int.natAbs ((a : ℤ) ^ m - (b : ℤ) ^ m) : ℝ) =
      (b : ℝ) ^ m - (a : ℝ) ^ m) := by
  have hle : a ^ m ≤ b ^ m := pow_le_pow_left₀ (Nat.cast_nonneg a) (by exact_mod_cast hab.le) m
  have hnat :
      Int.natAbs ((a : ℤ) ^ m - (b : ℤ) ^ m) = b ^ m - a ^ m := by
    simpa [Int.natCast_pow] using Int.natAbs_natCast_sub_natCast_of_le hle
  rw [hnat]
  norm_num [Nat.cast_sub hle]

lemma xi_time_part69_localized_rational_endomorphism_growth_rate_ratio_tendsto_one_of_lt
    {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    Tendsto
      (fun n : ℕ =>
        (Int.natAbs ((a : ℤ) ^ (n + 1) - (b : ℤ) ^ (n + 1)) : ℝ) /
          (b : ℝ) ^ (n + 1))
      atTop (𝓝 1) := by
  have hb : 0 < b := lt_trans ha hab
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hratio_nonneg : 0 ≤ (a : ℝ) / (b : ℝ) := div_nonneg (by positivity) hbR.le
  have hratio_lt_one : (a : ℝ) / (b : ℝ) < 1 := by
    exact (div_lt_one hbR).2 (by exact_mod_cast hab)
  have hpow :
      Tendsto (fun n : ℕ => ((a : ℝ) / (b : ℝ)) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nonneg hratio_lt_one).comp
      (tendsto_add_atTop_nat 1)
  have hmain :
      Tendsto (fun n : ℕ => 1 - ((a : ℝ) / (b : ℝ)) ^ (n + 1)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hpow
  refine hmain.congr' ?_
  filter_upwards with n
  have hden : (b : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ hbR.ne'
  rw [xi_time_part69_localized_rational_endomorphism_growth_rate_pow_gap_cast_of_lt
    (m := n + 1) hab]
  rw [div_pow]
  field_simp [hden, hbR.ne']

lemma xi_time_part69_localized_rational_endomorphism_growth_rate_dominant_power_tendsto_atTop
    {b : ℕ} (hb : 1 < b) :
    Tendsto (fun n : ℕ => (b : ℝ) ^ (n + 1)) atTop atTop := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  exact (tendsto_pow_atTop_atTop_of_one_lt hbR).comp (tendsto_add_atTop_nat 1)

lemma xi_time_part69_localized_rational_endomorphism_growth_rate_log_dominant_normalized
    {b : ℕ} (_hb : 0 < b) :
    Tendsto (fun n : ℕ => Real.log ((b : ℝ) ^ (n + 1)) / ((n + 1 : ℕ) : ℝ)) atTop
      (𝓝 (Real.log (b : ℝ))) := by
  have heq :
      (fun n : ℕ => Real.log ((b : ℝ) ^ (n + 1)) / ((n + 1 : ℕ) : ℝ)) =
        fun _ : ℕ => Real.log (b : ℝ) := by
    funext n
    have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    rw [Real.log_pow]
    field_simp [hn]
  rw [heq]
  exact tendsto_const_nhds

lemma xi_time_part69_localized_rational_endomorphism_growth_rate_tendsto_of_lt
    {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    Tendsto
      (fun n : ℕ =>
        (1 : ℝ) / (n + 1) *
          Real.log ((Int.natAbs ((a : ℤ) ^ (n + 1) - (b : ℤ) ^ (n + 1)) : ℝ)))
      atTop (𝓝 (Real.log (b : ℝ))) := by
  have hb : 0 < b := lt_trans ha hab
  have hb_one : 1 < b := by omega
  let f : ℕ → ℝ :=
    fun n => (Int.natAbs ((a : ℤ) ^ (n + 1) - (b : ℤ) ^ (n + 1)) : ℝ)
  let g : ℕ → ℝ := fun n => (b : ℝ) ^ (n + 1)
  have hg_ne : ∀ᶠ n in atTop, g n ≠ 0 := by
    filter_upwards with n
    exact pow_ne_zero _ (by positivity : (b : ℝ) ≠ 0)
  have hfg : f ~[atTop] g := by
    rw [Asymptotics.isEquivalent_iff_tendsto_one hg_ne]
    simpa [f, g, Pi.div_apply] using
      xi_time_part69_localized_rational_endomorphism_growth_rate_ratio_tendsto_one_of_lt
        (a := a) (b := b) ha hab
  have hg_top : Tendsto g atTop atTop :=
    xi_time_part69_localized_rational_endomorphism_growth_rate_dominant_power_tendsto_atTop hb_one
  have hlog_equiv : (fun n : ℕ => Real.log (f n)) ~[atTop] fun n : ℕ => Real.log (g n) :=
    hfg.log hg_top
  have hlogg_ne : ∀ᶠ n in atTop, Real.log (g n) ≠ 0 := by
    filter_upwards with n
    have hg_gt_one : 1 < g n := by
      have hbR : (1 : ℝ) < b := by exact_mod_cast hb_one
      exact one_lt_pow₀ hbR (by omega : n + 1 ≠ 0)
    exact (Real.log_pos hg_gt_one).ne'
  have hlog_ratio :
      Tendsto (fun n : ℕ => Real.log (f n) / Real.log (g n)) atTop (𝓝 1) := by
    simpa [Pi.div_apply] using
      (Asymptotics.isEquivalent_iff_tendsto_one hlogg_ne).1 hlog_equiv
  have hlogg_norm :
      Tendsto (fun n : ℕ => Real.log (g n) / ((n + 1 : ℕ) : ℝ)) atTop
        (𝓝 (Real.log (b : ℝ))) := by
    simpa [g] using
      xi_time_part69_localized_rational_endomorphism_growth_rate_log_dominant_normalized hb
  have hmul :
      Tendsto
        (fun n : ℕ =>
          (Real.log (f n) / Real.log (g n)) *
            (Real.log (g n) / ((n + 1 : ℕ) : ℝ)))
        atTop (𝓝 (Real.log (b : ℝ))) := by
    simpa using hlog_ratio.mul hlogg_norm
  refine hmul.congr' ?_
  filter_upwards [hlogg_ne] with n hlogg
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  calc
    Real.log (f n) / Real.log (g n) * (Real.log (g n) / ((n + 1 : ℕ) : ℝ)) =
        Real.log (f n) / ((n + 1 : ℕ) : ℝ) := by
      field_simp [hlogg, hn]
    _ =
        (1 : ℝ) / (n + 1) *
          Real.log ((Int.natAbs ((a : ℤ) ^ (n + 1) - (b : ℤ) ^ (n + 1)) : ℝ)) := by
      simp [f, div_eq_mul_inv, mul_comm]

/-- Paper label: `thm:xi-time-part69-localized-rational-endomorphism-growth-rate`. -/
theorem paper_xi_time_part69_localized_rational_endomorphism_growth_rate (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Filter.Tendsto
      (fun n : ℕ =>
        (1 : ℝ) / (n + 1) *
          Real.log ((Int.natAbs ((a : ℤ) ^ (n + 1) - (b : ℤ) ^ (n + 1)) : ℝ)))
      Filter.atTop (nhds (Real.log (max (a : ℝ) (b : ℝ)))) := by
  rcases lt_or_gt_of_ne hab with hab_lt | hba_lt
  · have hlim :=
      xi_time_part69_localized_rational_endomorphism_growth_rate_tendsto_of_lt
        (a := a) (b := b) ha hab_lt
    have hmax : max (a : ℝ) (b : ℝ) = b := by
      exact max_eq_right (by exact_mod_cast hab_lt.le)
    simpa [hmax] using hlim
  · have hlim :=
      xi_time_part69_localized_rational_endomorphism_growth_rate_tendsto_of_lt
        (a := b) (b := a) hb hba_lt
    have hseq_eq :
        (fun n : ℕ =>
          (1 : ℝ) / (n + 1) *
            Real.log ((Int.natAbs ((a : ℤ) ^ (n + 1) - (b : ℤ) ^ (n + 1)) : ℝ))) =
          fun n : ℕ =>
            (1 : ℝ) / (n + 1) *
              Real.log ((Int.natAbs ((b : ℤ) ^ (n + 1) - (a : ℤ) ^ (n + 1)) : ℝ)) := by
      funext n
      rw [show (a : ℤ) ^ (n + 1) - (b : ℤ) ^ (n + 1) =
          -((b : ℤ) ^ (n + 1) - (a : ℤ) ^ (n + 1)) by ring, Int.natAbs_neg]
    have hmax : max (a : ℝ) (b : ℝ) = a := by
      exact max_eq_left (by exact_mod_cast hba_lt.le)
    rw [hseq_eq]
    simpa [hmax] using hlim

end Omega.Zeta
