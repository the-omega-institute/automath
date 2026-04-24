import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter Topology

/-- The two ratio formulas agree pointwise once the anomaly-block and abelianization dimensions
are rewritten using the audited counting identities. -/
lemma conclusion_minimal_anomaly_block_relative_rank_phi_square_inverse_ratio_eq
    (minBlockDim abDim minCount totalCount : ℕ → ℕ)
    (hMin : ∀ m, minBlockDim m = minCount m)
    (hAb : ∀ m, abDim m = totalCount m) :
    (fun m => (minBlockDim m : ℝ) / abDim m) = fun m => (minCount m : ℝ) / totalCount m := by
  funext m
  rw [hMin m, hAb m]

/-- Rewriting the numerator and denominator by the audited identities transports the assumed
`φ⁻²` ratio limit to the anomaly-block/abelianization ratio.
    cor:conclusion-minimal-anomaly-block-relative-rank-phi-square-inverse -/
theorem paper_conclusion_minimal_anomaly_block_relative_rank_phi_square_inverse
    (φ : ℝ) (minBlockDim abDim minCount totalCount : ℕ → ℕ)
    (hMin : ∀ m, minBlockDim m = minCount m)
    (hAb : ∀ m, abDim m = totalCount m)
    (hLimit : Filter.Tendsto (fun m => (minCount m : ℝ) / totalCount m) Filter.atTop
      (𝓝 (φ ^ (-2 : ℤ)))) :
    Filter.Tendsto (fun m => (minBlockDim m : ℝ) / abDim m) Filter.atTop
      (𝓝 (φ ^ (-2 : ℤ))) := by
  simpa [conclusion_minimal_anomaly_block_relative_rank_phi_square_inverse_ratio_eq
    minBlockDim abDim minCount totalCount hMin hAb] using hLimit

end Omega.Conclusion
