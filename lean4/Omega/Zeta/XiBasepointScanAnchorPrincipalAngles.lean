import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.XiBasepointScanFullRankWeightGaugeInvariance

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `prop:xi-basepoint-scan-anchor-principal-angles`. Once the anchor Gram
determinant is factored into the weight product and the squared Cauchy determinant, any
principal-angle formula for the correlation determinant immediately yields the claimed product of
squared sine factors. -/
theorem paper_xi_basepoint_scan_anchor_principal_angles {kappa : ℕ}
    (D : XiBasepointAnchorData kappa kappa)
    (hdet : D.anchorFrame.det ≠ 0)
    (hwt : ∀ j, 0 < D.weights j)
    (theta : Fin kappa → ℝ)
    (hprincipal :
      D.anchorCauchyMatrix.det ^ (2 : ℕ) =
        ∏ j, (((Real.sin (theta j)) ^ (2 : ℕ) : ℝ) : ℂ)) :
    D.anchorGram.det =
      ((∏ j, ((D.weights j : ℝ) : ℂ)) : ℂ) *
        ∏ j, (((Real.sin (theta j)) ^ (2 : ℕ) : ℝ) : ℂ) := by
  rcases paper_xi_basepoint_scan_full_rank_weight_gauge_invariance D hdet hwt with
    ⟨_, _, hgram⟩
  calc
    D.anchorGram.det =
        ((∏ j, ((D.weights j : ℝ) : ℂ)) : ℂ) * D.anchorCauchyMatrix.det ^ (2 : ℕ) := hgram
    _ = ((∏ j, ((D.weights j : ℝ) : ℂ)) : ℂ) *
          ∏ j, (((Real.sin (theta j)) ^ (2 : ℕ) : ℝ) : ℂ) := by rw [hprincipal]

end Omega.Zeta
