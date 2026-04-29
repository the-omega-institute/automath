import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Product of squared absolute monic-anchor values at the pole roots. -/
noncomputable def xi_basepoint_scan_anchor_det_resultant_anchorProduct
    {κ : ℕ} (anchorAtPole : Fin κ → ℂ) : ℝ :=
  ∏ k : Fin κ, Complex.normSq (anchorAtPole k)

/-- Concrete resultant substitution in the full-rank anchored Gram determinant formula. -/
def xi_basepoint_scan_anchor_det_resultant_statement : Prop :=
  ∀ {κ : ℕ} (gramDet leadingConstant resultant : ℝ) (anchorAtPole : Fin κ → ℂ),
    resultant = xi_basepoint_scan_anchor_det_resultant_anchorProduct anchorAtPole →
      gramDet = leadingConstant / resultant →
        gramDet =
          leadingConstant /
            xi_basepoint_scan_anchor_det_resultant_anchorProduct anchorAtPole

/-- Paper label: `cor:xi-basepoint-scan-anchor-det-resultant`. -/
theorem paper_xi_basepoint_scan_anchor_det_resultant :
    xi_basepoint_scan_anchor_det_resultant_statement := by
  intro κ gramDet leadingConstant resultant anchorAtPole hresultant hgram
  rw [hgram, hresultant]

end Omega.Zeta
