import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinTwoStateAsymptotic

open Filter Topology

namespace Omega.Folding

/-- Limiting mass of the last-bit `0` atom in the two-state bin-fold model. -/
noncomputable def foldBinFDivergenceLimitZeroMass : ℝ :=
  1 / Real.goldenRatio

/-- Limiting mass of the last-bit `1` atom in the two-state bin-fold model. -/
noncomputable def foldBinFDivergenceLimitOneMass : ℝ :=
  1 / Real.goldenRatio ^ 2

/-- Explicit normalized ratio on the last-bit `0` atom coming from the two-state asymptotic. -/
noncomputable def foldBinFDivergenceRatioZero (m : ℕ) : ℝ :=
  1 + (Real.goldenRatio / 2) ^ m

/-- Explicit normalized ratio on the last-bit `1` atom coming from the two-state asymptotic. -/
noncomputable def foldBinFDivergenceRatioOne (m : ℕ) : ℝ :=
  1 - Real.goldenRatio * (Real.goldenRatio / 2) ^ m

/-- Two-point `f`-divergence against the limiting Bernoulli law. -/
noncomputable def foldBinFDivergence (f : ℝ → ℝ) (m : ℕ) : ℝ :=
  foldBinFDivergenceLimitZeroMass * f (foldBinFDivergenceRatioZero m) +
    foldBinFDivergenceLimitOneMass * f (foldBinFDivergenceRatioOne m)

/-- The two-state bin-fold asymptotic collapses every continuous two-point `f`-divergence to the
Bernoulli limit: the explicit last-bit ratios converge to `1`, so the divergence vanishes when
`f(1) = 0`.
    prop:fold-bin-f-divergence-collapse -/
theorem paper_fold_bin_f_divergence_collapse
    (D : FoldBinTwoStateAsymptoticData) {f : ℝ → ℝ} (hf : Continuous f) (hf1 : f 1 = 0) :
    Tendsto (foldBinFDivergence f) atTop (𝓝 0) := by
  let _hTwoState := paper_fold_bin_two_state_asymptotic D
  have hratio_lt_one : |Real.goldenRatio / 2| < 1 := by
    rw [abs_of_nonneg]
    · nlinarith [Real.goldenRatio_lt_two]
    · positivity
  have hpow :
      Tendsto (fun m : ℕ => (Real.goldenRatio / 2) ^ m) atTop (𝓝 0) := by
    exact _root_.tendsto_pow_atTop_nhds_zero_of_abs_lt_one hratio_lt_one
  have hZeroRatio :
      Tendsto (fun m : ℕ => foldBinFDivergenceRatioZero m) atTop (𝓝 1) := by
    unfold foldBinFDivergenceRatioZero
    simpa using tendsto_const_nhds.add hpow
  have hOneRatio :
      Tendsto (fun m : ℕ => foldBinFDivergenceRatioOne m) atTop (𝓝 1) := by
    unfold foldBinFDivergenceRatioOne
    have hScaled :
        Tendsto (fun m : ℕ => Real.goldenRatio * (Real.goldenRatio / 2) ^ m) atTop (𝓝 0) := by
      simpa using hpow.const_mul Real.goldenRatio
    simpa [sub_eq_add_neg] using tendsto_const_nhds.sub hScaled
  have hZeroTerm :
      Tendsto (fun m : ℕ => f (foldBinFDivergenceRatioZero m)) atTop (𝓝 0) := by
    have hCont : Tendsto (fun m : ℕ => f (foldBinFDivergenceRatioZero m)) atTop (𝓝 (f 1)) := by
      exact ((hf.continuousAt : ContinuousAt f 1).tendsto).comp hZeroRatio
    simpa [hf1] using hCont
  have hOneTerm :
      Tendsto (fun m : ℕ => f (foldBinFDivergenceRatioOne m)) atTop (𝓝 0) := by
    have hCont : Tendsto (fun m : ℕ => f (foldBinFDivergenceRatioOne m)) atTop (𝓝 (f 1)) := by
      exact ((hf.continuousAt : ContinuousAt f 1).tendsto).comp hOneRatio
    simpa [hf1] using hCont
  have hLeft :
      Tendsto
        (fun m : ℕ => foldBinFDivergenceLimitZeroMass * f (foldBinFDivergenceRatioZero m)) atTop
        (𝓝 0) := by
    simpa using hZeroTerm.const_mul foldBinFDivergenceLimitZeroMass
  have hRight :
      Tendsto
        (fun m : ℕ => foldBinFDivergenceLimitOneMass * f (foldBinFDivergenceRatioOne m)) atTop
        (𝓝 0) := by
    simpa using hOneTerm.const_mul foldBinFDivergenceLimitOneMass
  simpa [foldBinFDivergence] using hLeft.add hRight

end Omega.Folding
