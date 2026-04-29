import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.SPG.LpSuperellipsoidDecodingMultiplicativeNoiseStability

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-serrin-lp-flux-log-stability-prime-ledger`. A symmetric
multiplicative bound on the recovered `a_i^p` coordinate turns into an additive logarithmic
stability estimate, and the prime-ledger exponent bound follows by dividing by `log p_i`. -/
theorem paper_conclusion_serrin_lp_flux_log_stability_prime_ledger
    (d : ℕ) {p ε exactAxisPower recoveredAxisPower primeBase exactExponent recoveredExponent : ℝ}
    (hp : 0 < p) (hε0 : 0 < ε) (hε1 : ε < 1) (hprimeBase : 1 < primeBase)
    (hexactAxisPower : 0 < exactAxisPower) (hrecoveredAxisPower : 0 < recoveredAxisPower)
    (hupper :
      recoveredAxisPower ≤ Omega.SPG.lpSuperellipsoidNoiseRatio ε * exactAxisPower)
    (hlower :
      exactAxisPower ≤ Omega.SPG.lpSuperellipsoidNoiseRatio ε * recoveredAxisPower)
    (hexactLedger :
      Real.log exactAxisPower = exactExponent * Real.log primeBase)
    (hrecoveredLedger :
      Real.log recoveredAxisPower = recoveredExponent * Real.log primeBase) :
    |Real.log recoveredAxisPower / p - Real.log exactAxisPower / p| ≤
        Real.log (Omega.SPG.lpSuperellipsoidNoiseRatio ε) / p ∧
      |recoveredExponent - exactExponent| ≤
        Real.log (Omega.SPG.lpSuperellipsoidNoiseRatio ε) / Real.log primeBase := by
  rcases Omega.SPG.paper_spg_lp_superellipsoid_decoding_multiplicative_noise_stability d hp hε0 hε1
    with ⟨hratio, hmargin⟩
  let ratio := Omega.SPG.lpSuperellipsoidNoiseRatio ε
  have hratio_pos : 0 < ratio := by
    dsimp [ratio, Omega.SPG.lpSuperellipsoidNoiseRatio]
    have hden : 0 < 1 - ε := by linarith
    positivity
  have hratio_ne : ratio ≠ 0 := ne_of_gt hratio_pos
  have hlog_ratio_pos : 0 < Real.log ratio := by
    simpa [ratio] using Real.log_pos hratio
  have hupper_log :
      Real.log recoveredAxisPower ≤ Real.log ratio + Real.log exactAxisPower := by
    have hright_pos : 0 < ratio * exactAxisPower := mul_pos hratio_pos hexactAxisPower
    have hlog := Real.log_le_log hrecoveredAxisPower hupper
    have hmul : Real.log (ratio * exactAxisPower) = Real.log ratio + Real.log exactAxisPower := by
      rw [Real.log_mul hratio_ne hexactAxisPower.ne']
    rw [hmul] at hlog
    exact hlog
  have hlower_log :
      Real.log exactAxisPower ≤ Real.log ratio + Real.log recoveredAxisPower := by
    have hright_pos : 0 < ratio * recoveredAxisPower := mul_pos hratio_pos hrecoveredAxisPower
    have hlog := Real.log_le_log hexactAxisPower hlower
    have hmul :
        Real.log (ratio * recoveredAxisPower) = Real.log ratio + Real.log recoveredAxisPower := by
      rw [Real.log_mul hratio_ne hrecoveredAxisPower.ne']
    rw [hmul] at hlog
    exact hlog
  have habs_log :
      |Real.log recoveredAxisPower - Real.log exactAxisPower| ≤ Real.log ratio := by
    refine abs_le.mpr ?_
    constructor
    · linarith
    · linarith
  have hlog_div :
      |(Real.log recoveredAxisPower - Real.log exactAxisPower) / p| ≤ Real.log ratio / p := by
    simpa [abs_div, abs_of_pos hp] using div_le_div_of_nonneg_right habs_log (le_of_lt hp)
  have haxis :
      |Real.log recoveredAxisPower / p - Real.log exactAxisPower / p| ≤ Real.log ratio / p := by
    have hrewrite :
        Real.log recoveredAxisPower / p - Real.log exactAxisPower / p =
          (Real.log recoveredAxisPower - Real.log exactAxisPower) / p := by
      ring
    simpa [hrewrite] using hlog_div
  have hlog_prime_pos : 0 < Real.log primeBase := Real.log_pos hprimeBase
  have hledger_diff :
      Real.log recoveredAxisPower - Real.log exactAxisPower =
        (recoveredExponent - exactExponent) * Real.log primeBase := by
    linarith
  have hledger_mul :
      |recoveredExponent - exactExponent| * Real.log primeBase ≤ Real.log ratio := by
    calc
      |recoveredExponent - exactExponent| * Real.log primeBase =
          |(recoveredExponent - exactExponent) * Real.log primeBase| := by
            rw [abs_mul, abs_of_nonneg (le_of_lt hlog_prime_pos)]
      _ = |Real.log recoveredAxisPower - Real.log exactAxisPower| := by
            rw [hledger_diff]
      _ ≤ Real.log ratio := habs_log
  have hprime :
      |recoveredExponent - exactExponent| ≤ Real.log ratio / Real.log primeBase := by
    exact (le_div_iff₀ hlog_prime_pos).2 hledger_mul
  simpa [ratio] using ⟨haxis, hprime⟩

end Omega.Conclusion
