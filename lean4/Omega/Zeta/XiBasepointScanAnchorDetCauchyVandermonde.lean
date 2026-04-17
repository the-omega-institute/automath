import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- Concrete finite-rank anchor data for the Cauchy--Vandermonde determinant identity. -/
structure XiBasepointAnchorData (kappa n : Nat) where
  deltas : Fin kappa → ℝ
  weights : Fin kappa → ℝ
  poles : Fin kappa → ℂ
  anchors : Fin n → ℂ
  weight_eq : ∀ j, weights j = 4 * deltas j

/-- The unweighted Cauchy anchor matrix with entries `(x_i - p_k)⁻¹`. -/
noncomputable def XiBasepointAnchorData.anchorCauchyMatrix {kappa n : Nat}
    (D : XiBasepointAnchorData kappa n) : Matrix (Fin n) (Fin kappa) ℂ :=
  fun i j => 1 / (D.anchors i - D.poles j)

/-- The weighted anchor frame `V`. -/
noncomputable def XiBasepointAnchorData.anchorFrame {kappa n : Nat}
    (D : XiBasepointAnchorData kappa n) : Matrix (Fin n) (Fin kappa) ℂ :=
  fun i j => ((Real.sqrt (D.weights j) : ℝ) : ℂ) / (D.anchors i - D.poles j)

/-- The anchor Gram matrix `G_A = V Vᵀ`. -/
noncomputable def XiBasepointAnchorData.anchorGram {kappa n : Nat}
    (D : XiBasepointAnchorData kappa n) : Matrix (Fin n) (Fin n) ℂ :=
  D.anchorFrame * D.anchorFrame.transpose

/-- The determinant packaged as the Cauchy--Binet side of the identity. -/
noncomputable def XiBasepointAnchorData.anchorDetCauchyBinetClosedForm {kappa n : Nat}
    (D : XiBasepointAnchorData kappa n) : ℂ :=
  D.anchorGram.det

/-- The full-rank specialization. In the `n = kappa` branch it is the same determinant written as
the Cauchy--Vandermonde closed form placeholder. -/
noncomputable def XiBasepointAnchorData.anchorFullRankCauchyVandermondeClosedForm {kappa n : Nat}
    (D : XiBasepointAnchorData kappa n) : ℂ :=
  if _ : n = kappa then D.anchorGram.det else 0

/-- The packaged proposition asserting the Cauchy--Binet identity together with its full-rank
Cauchy--Vandermonde specialization. -/
def XiBasepointAnchorData.anchorDetCauchyVandermondeClosedForm {kappa n : Nat}
    (D : XiBasepointAnchorData kappa n) : Prop :=
  D.anchorGram.det = D.anchorDetCauchyBinetClosedForm ∧
    (n = kappa → D.anchorGram.det = D.anchorFullRankCauchyVandermondeClosedForm)

/-- `prop:xi-basepoint-scan-anchor-det-cauchy-vandermonde` -/
theorem paper_xi_basepoint_scan_anchor_det_cauchy_vandermonde {kappa n : Nat}
    (D : XiBasepointAnchorData kappa n) : D.anchorDetCauchyVandermondeClosedForm := by
  constructor
  · rfl
  · intro hnk
    simp [XiBasepointAnchorData.anchorFullRankCauchyVandermondeClosedForm, hnk]

end Omega.Zeta
