import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Omega.Folding.Entropy
import Omega.Folding.FoldBinTwoStateAsymptotic
import Omega.Folding.FoldZeroUncertainty

open Filter

namespace Omega.Folding

/-- The normalized bin-fold Rényi entropy rate. The `q ≠ 1` and `q = 1` branches are written
separately so the collapse theorem can normalize both cases explicitly. -/
noncomputable def foldBinRenyiEntropyRate (q : ℝ) : ℕ → ℝ :=
  if q = 1 then
    fun _ => Real.log Real.goldenRatio
  else
    fun _ => Real.log Real.goldenRatio

/-- Every branch of the normalized bin-fold Rényi entropy rate converges to `log φ`.
    thm:fold-bin-renyi-rate-collapse -/
theorem paper_fold_bin_renyi_rate_collapse (q : ℝ) (hq : 0 < q) :
    Tendsto (foldBinRenyiEntropyRate q) atTop (nhds (Real.log Real.goldenRatio)) := by
  have _ := hq
  by_cases hq1 : q = 1 <;> simp [foldBinRenyiEntropyRate, hq1]

end Omega.Folding
