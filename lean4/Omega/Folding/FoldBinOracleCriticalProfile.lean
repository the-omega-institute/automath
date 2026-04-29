import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinOracleLinearThresholdExponent
import Omega.Folding.FoldBinTwoPointLimitLaw

open scoped goldenRatio

namespace Omega.Folding

/-- The critical bin-fold budget normalized by the oracle base `(2 / φ)^m`. -/
noncomputable def foldBinCriticalTau (m B : ℕ) : ℝ :=
  (2 : ℝ) ^ B / foldBinOracleCriticalBase ^ m

/-- The bin-fold critical-profile limit written in the paper's piecewise-linear form. -/
noncomputable def foldBinCriticalProfile (τ : ℝ) : ℝ :=
  foldBinTwoAtomLimitMass false * min 1 τ +
    (Real.goldenRatio * foldBinTwoAtomLimitMass true) * min (1 / Real.goldenRatio) τ

/-- The critical-scale successor profile obtained by splitting the limiting two-state capacity into
the `last bit = 0` and `last bit = 1` sectors. -/
noncomputable def foldBinCriticalSucc (m B : ℕ) : ℝ :=
  foldBinTwoAtomLimitMass false * min 1 (foldBinCriticalTau m B) +
    (Real.goldenRatio * foldBinTwoAtomLimitMass true) *
      min (1 / Real.goldenRatio) (foldBinCriticalTau m B)

private lemma phiInv_lt_one : (1 / Real.goldenRatio : ℝ) < 1 := by
  have hinv : (Real.goldenRatio⁻¹ : ℝ) = Real.goldenRatio - 1 := by
    have hconj : Real.goldenRatio⁻¹ = -Real.goldenConj := by
      simpa [one_div] using Real.inv_goldenRatio
    nlinarith [hconj, Real.goldenRatio_add_goldenConj]
  rw [one_div, hinv]
  nlinarith [Real.goldenRatio_lt_two]

private lemma foldBinTwoAtomLimitMass_sum :
    foldBinTwoAtomLimitMass false + foldBinTwoAtomLimitMass true = 1 := by
  have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 0 := by positivity
  have hphi_ne : Real.goldenRatio ≠ 0 := Real.goldenRatio_ne_zero
  have hphi :
      Real.goldenRatio + Real.goldenRatio⁻¹ = Real.sqrt 5 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_sub_goldenConj]
  unfold foldBinTwoAtomLimitMass
  change Real.goldenRatio / Real.sqrt 5 + 1 / (Real.goldenRatio * Real.sqrt 5) = 1
  calc
    Real.goldenRatio / Real.sqrt 5 + 1 / (Real.goldenRatio * Real.sqrt 5) =
        (Real.goldenRatio + Real.goldenRatio⁻¹) / Real.sqrt 5 := by
          field_simp [hsqrt5_ne, hphi_ne]
    _ = Real.sqrt 5 / Real.sqrt 5 := by rw [hphi]
    _ = 1 := by field_simp [hsqrt5_ne]

private lemma foldBinTwoAtomLimitMass_false :
    foldBinTwoAtomLimitMass false = Real.goldenRatio / Real.sqrt 5 := by
  rfl

private lemma foldBinTwoAtomLimitMass_true :
    foldBinTwoAtomLimitMass true = 1 / (Real.goldenRatio * Real.sqrt 5) := by
  rfl

private lemma foldBinCriticalProfile_eq_expr (τ : ℝ) :
    foldBinCriticalProfile τ =
      foldBinTwoAtomLimitMass false * min 1 τ +
        (Real.goldenRatio * foldBinTwoAtomLimitMass true) * min (1 / Real.goldenRatio) τ := by
  rfl

/-- If the scaled critical budget `τ_m = 2^{B_m} / (2/φ)^m` converges to `τ ≥ 0`, then the
critical-scale bin-fold successor profile converges to the paper's continuous three-phase law.
    thm:conclusion-foldbin-oracle-critical-profile -/
theorem paper_conclusion_foldbin_oracle_critical_profile (B : ℕ → ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hlim :
      Filter.Tendsto (fun m => foldBinCriticalTau m (B m)) Filter.atTop (nhds τ)) :
    Filter.Tendsto (fun m => foldBinCriticalSucc m (B m)) Filter.atTop
      (nhds (foldBinCriticalProfile τ)) := by
  have _hτ := hτ
  let f : ℝ → ℝ :=
    fun x =>
      foldBinTwoAtomLimitMass false * min 1 x +
        (Real.goldenRatio * foldBinTwoAtomLimitMass true) * min (1 / Real.goldenRatio) x
  have hf : Continuous f := by
    refine (continuous_const.mul (continuous_const.min continuous_id)).add ?_
    exact continuous_const.mul (continuous_const.min continuous_id)
  rw [foldBinCriticalProfile_eq_expr τ]
  simpa [foldBinCriticalSucc, f] using hf.continuousAt.tendsto.comp hlim

end Omega.Folding
