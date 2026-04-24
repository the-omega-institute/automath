import Omega.Zeta.XiBasepointScanAnchorDetCauchyVandermonde
import Omega.Zeta.XiBasepointScanFullRankWeightGaugeInvariance

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete anchor data for the closed-form weight/shape separation package. -/
def xi_basepoint_scan_leverage_gap_codim1_closed_form_anchor_data {kappa : ℕ}
    (deltas weights : Fin kappa → ℝ) (poles anchors : Fin kappa → ℂ)
    (hweight : ∀ j, weights j = 4 * deltas j) : XiBasepointAnchorData kappa kappa where
  deltas := deltas
  weights := weights
  poles := poles
  anchors := anchors
  weight_eq := hweight

/-- Paper label: `thm:xi-basepoint-scan-leverage-gap-codim1-closed-form`.

In the finite full-rank scan model, the anchor determinant package gives the Cauchy--Vandermonde
closed form, while the weight-gauge identity separates the Gram determinant into a pure weight
factor and a pure Cauchy-shape factor. -/
theorem paper_xi_basepoint_scan_leverage_gap_codim1_closed_form {kappa : ℕ}
    (deltas weights : Fin kappa → ℝ) (poles anchors : Fin kappa → ℂ)
    (hweight : ∀ j, weights j = 4 * deltas j)
    (hwt : ∀ j, 0 < weights j)
    (hdet :
      (xi_basepoint_scan_leverage_gap_codim1_closed_form_anchor_data
        deltas weights poles anchors hweight).anchorFrame.det ≠ 0) :
    let D :=
      xi_basepoint_scan_leverage_gap_codim1_closed_form_anchor_data
        deltas weights poles anchors hweight
    D.anchorDetCauchyVandermondeClosedForm ∧
      D.anchorGram.det =
        ((∏ j, ((D.weights j : ℝ) : ℂ)) : ℂ) * D.anchorCauchyMatrix.det ^ (2 : ℕ) := by
  let D :=
    xi_basepoint_scan_leverage_gap_codim1_closed_form_anchor_data
      deltas weights poles anchors hweight
  have hdet' : D.anchorFrame.det ≠ 0 := by
    simpa [D, xi_basepoint_scan_leverage_gap_codim1_closed_form_anchor_data] using hdet
  have hcv : D.anchorDetCauchyVandermondeClosedForm :=
    paper_xi_basepoint_scan_anchor_det_cauchy_vandermonde D
  have hgauge := paper_xi_basepoint_scan_full_rank_weight_gauge_invariance D hdet' hwt
  rcases hgauge with ⟨_, _, hgram⟩
  simpa [D] using
    (show D.anchorDetCauchyVandermondeClosedForm ∧
        D.anchorGram.det =
          ((∏ j, ((D.weights j : ℝ) : ℂ)) : ℂ) * D.anchorCauchyMatrix.det ^ (2 : ℕ) from
      ⟨hcv, hgram⟩)

end Omega.Zeta
