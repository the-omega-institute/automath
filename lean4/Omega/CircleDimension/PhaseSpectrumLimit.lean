import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Omega.CircleDimension.CircleDim

open Filter

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: the phase-spectrum limit theorem is controlled by the coprime/divisible
    dichotomy for `phaseSpectrumCount`, together with the free case `t = 0`.
    thm:cdim-phase-spectrum-limit -/
theorem paper_cdim_phase_spectrum_limit_seeds :
    (∀ r t N : Nat, Nat.Coprime t N → phaseSpectrumCount r t N = N ^ r) ∧
      (∀ r N : Nat, phaseSpectrumCount r 0 N = N ^ (r + 1)) ∧
      (∀ r t p : Nat, Nat.Prime p → p ∣ t → phaseSpectrumCount r t p = p ^ (r + 1)) ∧
      (∀ r t p : Nat, Nat.Prime p → ¬ p ∣ t → phaseSpectrumCount r t p = p ^ r) := by
  refine ⟨phaseSpectrumCount_coprime, phaseSpectrumCount_free, ?_, ?_⟩
  · intro r t p hp hpt
    simpa [Nat.add_comm] using phaseSpectrumCount_prime_dvd r t hp hpt
  · intro r t p hp hpt
    exact phaseSpectrumCount_prime_ndvd r t hp hpt

/-- Paper label: `thm:cdim-phase-spectrum-limit`. -/
theorem paper_cdim_phase_spectrum_limit (r t : Nat) :
    Filter.Tendsto
      (fun N : Nat => Real.log (phaseSpectrumCount r t N : ℝ) / Real.log (N : ℝ))
      Filter.atTop (nhds (if t = 0 then (r + 1 : ℝ) else (r : ℝ))) := by
  by_cases ht : t = 0
  · subst t
    have hEventually :
        (fun N : Nat =>
          Real.log (phaseSpectrumCount r 0 N : ℝ) / Real.log (N : ℝ)) =ᶠ[atTop]
            (fun _ : Nat => (r + 1 : ℝ)) := by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hNgt_one : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
      have hlog_ne : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hNgt_one).ne'
      calc
        Real.log (phaseSpectrumCount r 0 N : ℝ) / Real.log (N : ℝ)
            = Real.log ((N ^ (r + 1) : Nat) : ℝ) / Real.log (N : ℝ) := by
                rw [phaseSpectrumCount_free]
        _ = ((r + 1 : ℕ) : ℝ) * Real.log (N : ℝ) / Real.log (N : ℝ) := by
                rw [Nat.cast_pow, Real.log_pow]
        _ = (r + 1 : ℝ) := by
                field_simp [hlog_ne]
                norm_num
    simpa using Filter.Tendsto.congr' hEventually.symm
      (tendsto_const_nhds : Filter.Tendsto (fun _ : Nat => (r + 1 : ℝ)) atTop
        (nhds (r + 1 : ℝ)))
  · have htpos_nat : 0 < t := Nat.pos_of_ne_zero ht
    have hcorr :
        Filter.Tendsto
          (fun N : Nat => Real.log (Nat.gcd t N : ℝ) / Real.log (N : ℝ))
          atTop (nhds (0 : ℝ)) := by
      have hupper :
          Filter.Tendsto (fun N : Nat => Real.log (t : ℝ) / Real.log (N : ℝ))
            atTop (nhds (0 : ℝ)) :=
        Filter.Tendsto.const_div_atTop
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) (Real.log (t : ℝ))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
      · filter_upwards [eventually_ge_atTop 2] with N hN
        have hNgt_one : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
        have hden_nonneg : 0 ≤ Real.log (N : ℝ) := le_of_lt (Real.log_pos hNgt_one)
        have hg_one : (1 : ℝ) ≤ (Nat.gcd t N : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (Nat.gcd_pos_of_pos_left N htpos_nat)
        have hnum_nonneg : 0 ≤ Real.log (Nat.gcd t N : ℝ) := Real.log_nonneg hg_one
        exact div_nonneg hnum_nonneg hden_nonneg
      · filter_upwards [eventually_ge_atTop 2] with N hN
        have hNpos_nat : 0 < N := by omega
        have hNgt_one : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
        have hden_nonneg : 0 ≤ Real.log (N : ℝ) := le_of_lt (Real.log_pos hNgt_one)
        have hgpos_real : 0 < (Nat.gcd t N : ℝ) := by
          exact_mod_cast Nat.gcd_pos_of_pos_left N htpos_nat
        have hg_le_t : (Nat.gcd t N : ℝ) ≤ (t : ℝ) := by
          exact_mod_cast Nat.gcd_le_left N htpos_nat
        have hlog_le : Real.log (Nat.gcd t N : ℝ) ≤ Real.log (t : ℝ) :=
          Real.log_le_log hgpos_real hg_le_t
        exact div_le_div_of_nonneg_right hlog_le hden_nonneg
    have hEventually :
        (fun N : Nat =>
          Real.log (phaseSpectrumCount r t N : ℝ) / Real.log (N : ℝ)) =ᶠ[atTop]
            (fun N : Nat =>
              (r : ℝ) + Real.log (Nat.gcd t N : ℝ) / Real.log (N : ℝ)) := by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hNpos_nat : 0 < N := by omega
      have hNgt_one : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
      have hlog_ne : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hNgt_one).ne'
      have hpow_ne : ((N : ℝ) ^ r) ≠ 0 := pow_ne_zero r (Nat.cast_ne_zero.mpr hNpos_nat.ne')
      have hg_ne : ((Nat.gcd t N : Nat) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.gcd_pos_of_pos_left N htpos_nat).ne'
      calc
        Real.log (phaseSpectrumCount r t N : ℝ) / Real.log (N : ℝ)
            = Real.log (((N : ℝ) ^ r) * (Nat.gcd t N : ℝ)) /
                Real.log (N : ℝ) := by
                simp [phaseSpectrumCount]
        _ = (Real.log ((N : ℝ) ^ r) + Real.log (Nat.gcd t N : ℝ)) /
              Real.log (N : ℝ) := by
                rw [Real.log_mul hpow_ne hg_ne]
        _ = ((r : ℝ) * Real.log (N : ℝ) + Real.log (Nat.gcd t N : ℝ)) /
              Real.log (N : ℝ) := by
                rw [Real.log_pow]
        _ = (r : ℝ) + Real.log (Nat.gcd t N : ℝ) / Real.log (N : ℝ) := by
                field_simp [hlog_ne]
    have hmain :
        Filter.Tendsto
          (fun N : Nat => (r : ℝ) + Real.log (Nat.gcd t N : ℝ) / Real.log (N : ℝ))
          atTop (nhds ((r : ℝ) + 0)) :=
      tendsto_const_nhds.add hcorr
    simpa [ht] using Filter.Tendsto.congr' hEventually.symm hmain

end Omega.CircleDimension
