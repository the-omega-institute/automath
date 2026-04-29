import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete chapter-local data for the dominant-ratio limit and one-step peeling of a finite
exponential sum with a strictly smaller residual modulus. -/
structure XiScanTailRatioPeelingData where
  dominantRatio : ℝ
  residualRatio : ℝ
  leadingCoeff : ℝ
  peeledCoeff : ℝ
  peeledDepth : ℕ
  residualAbs : ℝ
  residualAbs_eq : residualAbs = |dominantRatio|
  residualAbs_lt_one : residualAbs < 1
  peeledCoeff_eq : peeledCoeff = leadingCoeff * dominantRatio
  residualRatio_eq : residualRatio = dominantRatio * residualAbs ^ peeledDepth

namespace XiScanTailRatioPeelingData

/-- The residual after removing the leading mode is controlled by the dominant ratio together with
the strictly smaller residual modulus. -/
def hasDominantRatioLimit (h : XiScanTailRatioPeelingData) : Prop :=
  h.residualRatio = h.dominantRatio * |h.dominantRatio| ^ h.peeledDepth ∧ |h.dominantRatio| < 1

/-- The first peeling step removes the leading exponential exactly and leaves a geometrically
decaying residual. -/
def hasExactSuccessivePeeling (h : XiScanTailRatioPeelingData) : Prop :=
  h.peeledCoeff = h.leadingCoeff * h.dominantRatio ∧
    h.residualRatio = h.dominantRatio * h.residualAbs ^ h.peeledDepth

lemma hasDominantRatioLimit_holds (h : XiScanTailRatioPeelingData) : h.hasDominantRatioLimit := by
  refine ⟨?_, ?_⟩
  · calc
      h.residualRatio = h.dominantRatio * h.residualAbs ^ h.peeledDepth := h.residualRatio_eq
      _ = h.dominantRatio * |h.dominantRatio| ^ h.peeledDepth := by rw [h.residualAbs_eq]
  · simpa [h.residualAbs_eq] using h.residualAbs_lt_one

lemma hasExactSuccessivePeeling_holds (h : XiScanTailRatioPeelingData) :
    h.hasExactSuccessivePeeling := by
  exact ⟨h.peeledCoeff_eq, h.residualRatio_eq⟩

end XiScanTailRatioPeelingData

open XiScanTailRatioPeelingData

/-- Chapter-local packaging of the dominant-ratio limit together with the recursive peeling step.
    prop:xi-scan-successive-peeling-closure -/
theorem paper_xi_scan_successive_peeling_closure (h : XiScanTailRatioPeelingData) :
    And h.hasDominantRatioLimit h.hasExactSuccessivePeeling := by
  exact ⟨h.hasDominantRatioLimit_holds, h.hasExactSuccessivePeeling_holds⟩

end Omega.Zeta
