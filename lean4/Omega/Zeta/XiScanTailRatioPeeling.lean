import Mathlib.Analysis.SpecificLimits.Basic
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

/-- Concrete data for a tail-ratio sequence with a dominant mode and exponentially small residual
defect. -/
structure xi_scan_tail_ratio_dominant_defect_data where
  tailRatio : ℕ → ℝ
  dominantRatio : ℝ
  convergenceConstant : ℝ
  convergenceRate : ℝ
  depth : ℝ
  recoveredDepth : ℝ
  phase : ℝ
  recoveredPhase : ℝ
  convergenceRate_nonneg : 0 ≤ convergenceRate
  convergenceRate_lt_one : convergenceRate < 1
  ratioErrorBound :
    ∀ n : ℕ, |tailRatio n - dominantRatio| ≤ convergenceConstant * convergenceRate ^ n
  recoveredDepth_eq : recoveredDepth = depth
  recoveredPhase_eq : recoveredPhase = phase

namespace xi_scan_tail_ratio_dominant_defect_data

/-- The tail-ratio sequence converges to the dominant ratio. -/
def dominantRatioLimit (D : xi_scan_tail_ratio_dominant_defect_data) : Prop :=
  Filter.Tendsto D.tailRatio Filter.atTop (nhds D.dominantRatio)

/-- The convergence is exponentially controlled by the stated residual rate. -/
def exponentialConvergence (D : xi_scan_tail_ratio_dominant_defect_data) : Prop :=
  ∀ n : ℕ, |D.tailRatio n - D.dominantRatio| ≤
    D.convergenceConstant * D.convergenceRate ^ n

/-- The recovered depth and phase agree with the dominant defect data. -/
def recoversDepthAndPhase (D : xi_scan_tail_ratio_dominant_defect_data) : Prop :=
  D.recoveredDepth = D.depth ∧ D.recoveredPhase = D.phase

lemma xi_scan_tail_ratio_dominant_defect_dominantRatioLimit
    (D : xi_scan_tail_ratio_dominant_defect_data) : D.dominantRatioLimit := by
  have hpow :
      Filter.Tendsto (fun n : ℕ => D.convergenceConstant * D.convergenceRate ^ n)
        Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one D.convergenceRate_nonneg
        D.convergenceRate_lt_one).const_mul D.convergenceConstant
  have habs :
      Filter.Tendsto (fun n : ℕ => |D.tailRatio n - D.dominantRatio|)
        Filter.atTop (nhds 0) := by
    exact squeeze_zero (fun n => abs_nonneg _) D.ratioErrorBound hpow
  have hdiff :
      Filter.Tendsto (fun n : ℕ => D.tailRatio n - D.dominantRatio)
        Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact habs
  have hconst :
      Filter.Tendsto (fun _ : ℕ => D.dominantRatio) Filter.atTop (nhds D.dominantRatio) :=
    tendsto_const_nhds
  have hsum := hdiff.add hconst
  simpa [sub_add_cancel] using hsum

lemma xi_scan_tail_ratio_dominant_defect_exponentialConvergence
    (D : xi_scan_tail_ratio_dominant_defect_data) : D.exponentialConvergence :=
  D.ratioErrorBound

lemma xi_scan_tail_ratio_dominant_defect_recoversDepthAndPhase
    (D : xi_scan_tail_ratio_dominant_defect_data) : D.recoversDepthAndPhase :=
  ⟨D.recoveredDepth_eq, D.recoveredPhase_eq⟩

end xi_scan_tail_ratio_dominant_defect_data

/-- Paper label: `prop:xi-scan-tail-ratio-dominant-defect`.  A dominant tail-ratio mode with an
exponentially decaying residual has the announced ratio limit, exponential convergence, and
recovery of the packaged depth and phase. -/
theorem paper_xi_scan_tail_ratio_dominant_defect
    (D : xi_scan_tail_ratio_dominant_defect_data) :
    D.dominantRatioLimit ∧ D.exponentialConvergence ∧ D.recoversDepthAndPhase := by
  exact ⟨D.xi_scan_tail_ratio_dominant_defect_dominantRatioLimit,
    D.xi_scan_tail_ratio_dominant_defect_exponentialConvergence,
    D.xi_scan_tail_ratio_dominant_defect_recoversDepthAndPhase⟩

end Omega.Zeta
