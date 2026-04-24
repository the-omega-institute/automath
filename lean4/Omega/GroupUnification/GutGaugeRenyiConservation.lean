import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Basic
import Omega.Folding.BinGaugeVolume
import Omega.Folding.FoldBinRenyiRateCollapse

namespace Omega.GroupUnification

open Filter
open scoped BigOperators

/-- The exact Shannon-side compensation term `m log 2 - κ_m`. -/
noncomputable def gutShannonEntropy {α : Type*} [Fintype α] (m : ℕ) (d : α → ℕ) : ℝ :=
  (m : ℝ) * Real.log 2 - Omega.Folding.binGaugeKappa m d

/-- The gauge-side leading rate complementary to the Rényi entropy rate `log φ`. -/
noncomputable def gutGaugeLeadingRate : ℝ :=
  Real.log 2 - Real.log Real.goldenRatio

/-- Publication-facing GUT wrapper: the bin-gauge interval becomes a Shannon conservation law
after rewriting `κ_m` as `m log 2 - H`, and the verified Rényi rate collapse packages the common
leading term `log 2`.
    thm:gut-gauge-renyi-conservation -/
theorem paper_gut_gauge_renyi_conservation {α : Type*} [Fintype α]
    (m : ℕ) (d : α → ℕ) (hd : ∀ a, 1 ≤ d a) (hsum : ∑ a, d a = 2 ^ m)
    (q : ℝ) (hq : 0 < q) :
    ((m : ℝ) * Real.log 2 - 1 ≤ Omega.Folding.binGaugeG m d + gutShannonEntropy m d ∧
      Omega.Folding.binGaugeG m d + gutShannonEntropy m d ≤ (m : ℝ) * Real.log 2) ∧
      Tendsto
        (fun n : ℕ => gutGaugeLeadingRate + Omega.Folding.foldBinRenyiEntropyRate q n)
        atTop (nhds (Real.log 2)) := by
  have hgauge := Omega.Folding.paper_fold_bin_gauge_volume m d hd hsum
  refine ⟨?_, ?_⟩
  · constructor
    · dsimp [gutShannonEntropy]
      linarith [hgauge.1]
    · dsimp [gutShannonEntropy]
      linarith [hgauge.2]
  · simpa [gutGaugeLeadingRate] using
      (Omega.Folding.paper_fold_bin_renyi_rate_collapse q hq).const_add
        (Real.log 2 - Real.log Real.goldenRatio)

end Omega.GroupUnification
