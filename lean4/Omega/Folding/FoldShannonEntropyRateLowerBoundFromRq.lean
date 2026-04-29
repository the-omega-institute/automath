import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

open Filter Topology

namespace Omega.Folding

noncomputable section

/-- Concrete data for transporting an order-`q` normalized power-sum growth rate into a Shannon
entropy-rate lower bound. -/
structure FoldShannonEntropyRateLowerBoundFromRqData where
  q : ℝ
  hq : 1 < q
  normalizedLogPowerSum : ℕ → ℝ
  shannonRate : ℕ → ℝ
  rqLimit : ℝ
  shannonLimit : ℝ
  renyiRate_le_shannonRate :
    ∀ m,
      ((q / (q - 1)) * Real.log 2 - (1 / (q - 1)) * normalizedLogPowerSum m) ≤ shannonRate m
  normalizedLogPowerSum_tendsto : Tendsto normalizedLogPowerSum atTop (𝓝 rqLimit)
  shannonRate_tendsto : Tendsto shannonRate atTop (𝓝 shannonLimit)

namespace FoldShannonEntropyRateLowerBoundFromRqData

/-- Order-`q` Rényi entropy rate written in terms of the normalized logarithm of `S_q`. -/
def fold_shannon_entropy_rate_lower_bound_from_rq_renyiRate
    (D : FoldShannonEntropyRateLowerBoundFromRqData) (m : ℕ) : ℝ :=
  (D.q / (D.q - 1)) * Real.log 2 - (1 / (D.q - 1)) * D.normalizedLogPowerSum m

/-- The lower bound predicted by the limiting order-`q` Rényi rate. -/
def fold_shannon_entropy_rate_lower_bound_from_rq_lowerBound
    (D : FoldShannonEntropyRateLowerBoundFromRqData) : ℝ :=
  (D.q / (D.q - 1)) * Real.log 2 - (1 / (D.q - 1)) * D.rqLimit

/-- The Shannon entropy-rate limit dominates the limiting order-`q` Rényi entropy rate. -/
def shannonEntropyRateLowerBound (D : FoldShannonEntropyRateLowerBoundFromRqData) : Prop :=
  D.fold_shannon_entropy_rate_lower_bound_from_rq_lowerBound ≤ D.shannonLimit

end FoldShannonEntropyRateLowerBoundFromRqData

/-- Paper label: `cor:fold-shannon-entropy-rate-lower-bound-from-rq`. If the normalized logarithm
of the order-`q` power sum `S_q` has limit `r_q` and Shannon dominates the order-`q` Rényi entropy
rate at every finite volume, then the Shannon entropy-rate limit is at least the corresponding
Rényi lower bound `(q/(q-1)) log 2 - r_q/(q-1)`. -/
theorem paper_fold_shannon_entropy_rate_lower_bound_from_rq
    (D : FoldShannonEntropyRateLowerBoundFromRqData) : D.shannonEntropyRateLowerBound := by
  have hconst :
      Tendsto (fun _ : ℕ => (D.q / (D.q - 1)) * Real.log 2) atTop
        (𝓝 ((D.q / (D.q - 1)) * Real.log 2)) :=
    tendsto_const_nhds
  have hmul :
      Tendsto
        (fun m => (1 / (D.q - 1)) * D.normalizedLogPowerSum m)
        atTop (𝓝 ((1 / (D.q - 1)) * D.rqLimit)) := by
    exact tendsto_const_nhds.mul D.normalizedLogPowerSum_tendsto
  have hrenyi_raw :
      Tendsto
        (fun m => (D.q / (D.q - 1)) * Real.log 2 - (1 / (D.q - 1)) * D.normalizedLogPowerSum m)
        atTop (𝓝 ((D.q / (D.q - 1)) * Real.log 2 - (1 / (D.q - 1)) * D.rqLimit)) := by
    exact hconst.sub hmul
  have hrenyi :
      Tendsto D.fold_shannon_entropy_rate_lower_bound_from_rq_renyiRate atTop
        (𝓝 D.fold_shannon_entropy_rate_lower_bound_from_rq_lowerBound) := by
    change Tendsto
      (fun m => (D.q / (D.q - 1)) * Real.log 2 - (1 / (D.q - 1)) * D.normalizedLogPowerSum m)
      atTop (𝓝 ((D.q / (D.q - 1)) * Real.log 2 - (1 / (D.q - 1)) * D.rqLimit))
    exact hrenyi_raw
  have hbound :=
    le_of_tendsto_of_tendsto' hrenyi D.shannonRate_tendsto D.renyiRate_le_shannonRate
  simpa [FoldShannonEntropyRateLowerBoundFromRqData.shannonEntropyRateLowerBound] using hbound

end

end Omega.Folding
