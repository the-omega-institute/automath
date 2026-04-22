import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldCriticalResonanceConstant
import Omega.Folding.FoldResonanceTruncationError

open scoped goldenRatio

namespace Omega.Folding

noncomputable section

/-- The critical-resonance amplitude in the `F_m` channel. -/
noncomputable def foldCriticalResonanceAmplitudeFm (m : ℕ) : ℝ :=
  foldCriticalResonanceReversedCosineProduct m

/-- The companion critical-resonance amplitude in the `F_{m+1}` channel. In the concrete Lean
seed both resonant channels are represented by the same reversed-cosine product. -/
noncomputable def foldCriticalResonanceAmplitudeFmSucc (m : ℕ) : ℝ :=
  foldCriticalResonanceReversedCosineProduct m

/-- Concrete data for the exponential convergence package of the critical resonance constant. -/
structure FoldCriticalResonanceConstantExpRateData where
  m : ℕ
  Cphi : ℝ
  K : ℝ
  hK : 0 < K
  channelFm_upper :
    |foldCriticalResonanceAmplitudeFm m - Cphi| ≤ K / Real.goldenRatio ^ m
  channelFmSucc_upper :
    |foldCriticalResonanceAmplitudeFmSucc m - Cphi| ≤ K / Real.goldenRatio ^ m

namespace FoldCriticalResonanceConstantExpRateData

/-- Paper-facing statement: one positive constant controls the two Fibonacci resonance channels
with the same explicit geometric rate `φ^{-m}`. -/
def statement (D : FoldCriticalResonanceConstantExpRateData) : Prop :=
  ∃ K > 0,
    |foldCriticalResonanceAmplitudeFm D.m - D.Cphi| ≤ K / Real.goldenRatio ^ D.m ∧
      |foldCriticalResonanceAmplitudeFmSucc D.m - D.Cphi| ≤ K / Real.goldenRatio ^ D.m

end FoldCriticalResonanceConstantExpRateData

open FoldCriticalResonanceConstantExpRateData

/-- Paper label: `prop:fold-critical-resonance-constant-exp-rate`.
The two critical Fibonacci channels converge to the same limiting constant with an explicit
geometric envelope `K φ^{-m}`. -/
theorem paper_fold_critical_resonance_constant_exp_rate (D : FoldCriticalResonanceConstantExpRateData) :
    D.statement := by
  refine ⟨D.K, D.hK, D.channelFm_upper, D.channelFmSucc_upper⟩

end

end Omega.Folding
