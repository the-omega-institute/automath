import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Natural-log information gap between the ambient cube and the Fold stable set. -/
def xi_fold_boundary_info_gap_same_scale_infoGapNat (m cardX : ℕ) : ℝ :=
  (m : ℝ) * Real.log 2 - Real.log (cardX : ℝ)

/-- Harper's edge-isoperimetric lower bound, in base-two logarithmic units. -/
def xi_fold_boundary_info_gap_same_scale_harperLower (m cardX : ℕ) : ℝ :=
  (cardX : ℝ) * (xi_fold_boundary_info_gap_same_scale_infoGapNat m cardX / Real.log 2)

/-- The shared golden-mean linear information scale, in nats. -/
def xi_fold_boundary_info_gap_same_scale_linearScaleNat (m : ℕ) : ℝ :=
  (m : ℝ) * (Real.log 2 - Real.log Real.goldenRatio)

/-- The same golden-mean linear information scale, in bits. -/
def xi_fold_boundary_info_gap_same_scale_linearScaleBits (m : ℕ) : ℝ :=
  xi_fold_boundary_info_gap_same_scale_linearScaleNat m / Real.log 2

/-- Coarse reversible-lift side-information lower bound. -/
def xi_fold_boundary_info_gap_same_scale_sideInfoLower (m cardX : ℕ) (M : ℝ) : ℝ :=
  xi_fold_boundary_info_gap_same_scale_infoGapNat m cardX / Real.log M - 1

/-- Paper label: `prop:xi-fold-boundary-info-gap-same-scale`.
Harper's hypercube edge-isoperimetric lower bound and the Fibonacci-cardinality logarithmic
asymptotic force both the boundary-per-vertex bound and the reversible-lift side-information
bound to share the same linear information-gap scale. -/
theorem paper_xi_fold_boundary_info_gap_same_scale
    (m boundaryEdges cardX : ℕ) (sideInfoLength M C : ℝ)
    (hcard_pos : 0 < cardX)
    (hharper :
      xi_fold_boundary_info_gap_same_scale_harperLower m cardX ≤ boundaryEdges)
    (hfibLog :
      |Real.log (cardX : ℝ) - (m : ℝ) * Real.log Real.goldenRatio| ≤ C)
    (hM : 1 < M)
    (hside :
      xi_fold_boundary_info_gap_same_scale_sideInfoLower m cardX M ≤ sideInfoLength) :
    xi_fold_boundary_info_gap_same_scale_harperLower m cardX ≤ boundaryEdges ∧
      xi_fold_boundary_info_gap_same_scale_linearScaleBits m - C / Real.log 2 ≤
        (boundaryEdges : ℝ) / (cardX : ℝ) ∧
      xi_fold_boundary_info_gap_same_scale_linearScaleNat m / Real.log M -
          C / Real.log M - 1 ≤ sideInfoLength := by
  have hcardR_pos : 0 < (cardX : ℝ) := by exact_mod_cast hcard_pos
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hlogM_pos : 0 < Real.log M := Real.log_pos hM
  have hfib_upper :
      Real.log (cardX : ℝ) ≤ (m : ℝ) * Real.log Real.goldenRatio + C := by
    linarith [(abs_le.mp hfibLog).2]
  have hgap_lower :
      xi_fold_boundary_info_gap_same_scale_linearScaleNat m - C ≤
        xi_fold_boundary_info_gap_same_scale_infoGapNat m cardX := by
    unfold xi_fold_boundary_info_gap_same_scale_linearScaleNat
      xi_fold_boundary_info_gap_same_scale_infoGapNat
    linarith
  have hbits_lower :
      xi_fold_boundary_info_gap_same_scale_linearScaleBits m - C / Real.log 2 ≤
        xi_fold_boundary_info_gap_same_scale_infoGapNat m cardX / Real.log 2 := by
    unfold xi_fold_boundary_info_gap_same_scale_linearScaleBits
    calc
      xi_fold_boundary_info_gap_same_scale_linearScaleNat m / Real.log 2 - C / Real.log 2 =
          (xi_fold_boundary_info_gap_same_scale_linearScaleNat m - C) / Real.log 2 := by
            ring
      _ ≤ xi_fold_boundary_info_gap_same_scale_infoGapNat m cardX / Real.log 2 := by
            exact div_le_div_of_nonneg_right hgap_lower hlog2_pos.le
  have hperVertex :
      xi_fold_boundary_info_gap_same_scale_infoGapNat m cardX / Real.log 2 ≤
        (boundaryEdges : ℝ) / (cardX : ℝ) := by
    exact (le_div_iff₀ hcardR_pos).2 (by
      simpa [xi_fold_boundary_info_gap_same_scale_harperLower, mul_comm] using hharper)
  have hside_scale :
      xi_fold_boundary_info_gap_same_scale_linearScaleNat m / Real.log M -
          C / Real.log M - 1 ≤
        xi_fold_boundary_info_gap_same_scale_sideInfoLower m cardX M := by
    unfold xi_fold_boundary_info_gap_same_scale_sideInfoLower
    calc
      xi_fold_boundary_info_gap_same_scale_linearScaleNat m / Real.log M -
          C / Real.log M - 1 =
          (xi_fold_boundary_info_gap_same_scale_linearScaleNat m - C) / Real.log M - 1 := by
            ring
      _ ≤ xi_fold_boundary_info_gap_same_scale_infoGapNat m cardX / Real.log M - 1 := by
            exact sub_le_sub_right
              (div_le_div_of_nonneg_right hgap_lower hlogM_pos.le) 1
  refine ⟨hharper, ?_, ?_⟩
  · exact le_trans hbits_lower hperVertex
  · exact le_trans hside_scale hside

end

end Omega.Zeta
