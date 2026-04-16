import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.Experiments.ParryBaselineGapSturmian

open Filter Asymptotics Topology
open Real

set_option maxHeartbeats 400000 in
/-- Paper-facing Sturmian-versus-Parry gap wrapper: if the folded support has size at most
    `m + 1`, every supported word has Parry mass at most the all-zero cylinder mass, and total
    variation is bounded below by the Parry mass outside the folded support, then the explicit
    lower bound follows.
    prop:parry-baseline-gap-sturmian -/
theorem paper_parry_baseline_gap_sturmian
    (m : ℕ)
    (tvDist supportMass zeroCylinderMass : ℝ)
    (hSupport : supportMass ≤ (m + 1 : ℝ) * zeroCylinderMass)
    (hTV : 1 - supportMass ≤ tvDist) :
    1 - (m + 1 : ℝ) * zeroCylinderMass ≤ tvDist := by
  linarith

/-- The Sturmian gap from `paper_parry_baseline_gap_sturmian` implies an explicit exponential
    upper bound for `1 - D_TV`, hence `D_TV → 1`.
    cor:parry-gap-exp -/
theorem paper_parry_gap_exp
    (tvDist supportMass : ℕ → ℝ)
    (π0 : ℝ)
    (hπ0 : 0 ≤ π0)
    (hSupport : ∀ m, supportMass m ≤ (m + 1 : ℝ) * (π0 * goldenRatio ^ (-(m - 1 : ℝ))))
    (hTV : ∀ m, 1 - supportMass m ≤ tvDist m)
    (hTV_upper : ∀ m, tvDist m ≤ 1) :
    (∀ m, 1 - tvDist m ≤ (m + 1 : ℝ) * π0 * goldenRatio ^ (-(m - 1 : ℝ))) ∧
      (∀ m : ℕ, 1 ≤ m →
        (m + 1 : ℝ) * π0 * goldenRatio ^ (-(m - 1 : ℝ)) ≤
          (2 * π0 * goldenRatio) * ((m : ℝ) * goldenRatio ^ (-(m : ℝ)))) ∧
      Tendsto tvDist atTop (𝓝 1) := by
  let gap : ℕ → ℝ := fun m => (m + 1 : ℝ) * π0 * goldenRatio ^ (-(m - 1 : ℝ))
  let rateInv : ℕ → ℝ := fun m => (m : ℝ) * (goldenRatio⁻¹ : ℝ) ^ m
  have hGapUpper : ∀ m, 1 - tvDist m ≤ gap m := by
    intro m
    have hLower :=
      paper_parry_baseline_gap_sturmian m (tvDist m) (supportMass m)
        (π0 * goldenRatio ^ (-(m - 1 : ℝ))) (hSupport m) (hTV m)
    dsimp [gap]
    nlinarith
  have hGapRate : ∀ m, 1 ≤ m →
      gap m ≤ (2 * π0 * goldenRatio) * ((m : ℝ) * goldenRatio ^ (-(m : ℝ))) := by
    intro m hm
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm) with ⟨k, rfl⟩
    dsimp [gap]
    have hk : (k : ℝ) + 2 ≤ 2 * ((k : ℝ) + 1) := by nlinarith
    have hexp : (-(↑(k + 1) - 1 : ℝ)) = 1 + (-(↑(k + 1) : ℝ)) := by
      norm_num
    rw [hexp, Real.rpow_add goldenRatio_pos, Real.rpow_one]
    calc
      (↑(k + 1) + 1) * π0 * (goldenRatio * goldenRatio ^ (-(↑(k + 1) : ℝ)))
          ≤ (2 * ↑(k + 1)) * π0 * (goldenRatio * goldenRatio ^ (-(↑(k + 1) : ℝ))) := by
            gcongr
            have hk' : (k : ℝ) + 1 + 1 ≤ 2 * ((k : ℝ) + 1) := by nlinarith
            simpa [Nat.cast_add, Nat.cast_one] using hk'
      _ = (2 * π0 * goldenRatio) * ((↑(k + 1) : ℝ) * goldenRatio ^ (-(↑(k + 1) : ℝ))) := by
            ring
  have hGapBigO : gap =O[atTop] fun m : ℕ => (m : ℝ) * goldenRatio ^ (-(m : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound (2 * π0 * goldenRatio) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hGapNonneg : 0 ≤ gap m := by
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm) with ⟨k, rfl⟩
      dsimp [gap]
      positivity
    have hRateNonneg : 0 ≤ (m : ℝ) * goldenRatio ^ (-(m : ℝ)) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hGapNonneg, Real.norm_eq_abs, abs_of_nonneg hRateNonneg]
    exact hGapRate m hm
  have hphiinv_nonneg : 0 ≤ (goldenRatio⁻¹ : ℝ) := by positivity
  have hphiinv_lt_one : (goldenRatio⁻¹ : ℝ) < 1 := by
    simpa using inv_lt_one_of_one_lt₀ one_lt_goldenRatio
  have hRateInv0 : Tendsto rateInv atTop (𝓝 0) := by
    dsimp [rateInv]
    simpa using tendsto_self_mul_const_pow_of_lt_one hphiinv_nonneg hphiinv_lt_one
  have hRateEq : rateInv =ᶠ[atTop] fun m : ℕ => (m : ℝ) * goldenRatio ^ (-(m : ℝ)) := by
    exact Filter.Eventually.of_forall fun m => by
      dsimp [rateInv]
      rw [Real.rpow_neg goldenRatio_pos.le, Real.rpow_natCast, inv_pow]
  have hRate0 : Tendsto (fun m : ℕ => (m : ℝ) * goldenRatio ^ (-(m : ℝ))) atTop (𝓝 0) := by
    exact Filter.Tendsto.congr' hRateEq hRateInv0
  have hGap0 : Tendsto gap atTop (𝓝 0) := hGapBigO.trans_tendsto hRate0
  have hOneMinus0 : Tendsto (fun m => 1 - tvDist m) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hGap0
    intro m
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hGapUpper m
    · linarith [hTV_upper m]
  have hTvOne : Tendsto (fun m => 1 - (1 - tvDist m)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hOneMinus0
  refine ⟨hGapUpper, hGapRate, ?_⟩
  simpa using hTvOne

end Omega.Experiments.ParryBaselineGapSturmian
