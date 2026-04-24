import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.Zeta.XiBasepointScanLeverageGapCodim1ClosedForm

namespace Omega.Zeta

open Polynomial
open scoped BigOperators

/-- The anchor polynomial `y_A(z) = ∏_{a ∈ A} (z - a)`. -/
noncomputable def xi_basepoint_scan_residual_kernel_polynomial_frame_yA
    (A : Finset ℂ) : Polynomial ℂ :=
  ∏ a ∈ A, (X - C a)

/-- In the codimension-one model there is a single residual quotient polynomial. -/
noncomputable def xi_basepoint_scan_residual_kernel_polynomial_frame_residual_quotient
    (_A : Finset ℂ) : Polynomial ℂ :=
  1

/-- Residual numerator polynomial. -/
noncomputable def xi_basepoint_scan_residual_kernel_polynomial_frame_residual_polynomial
    (A : Finset ℂ) : Polynomial ℂ :=
  xi_basepoint_scan_residual_kernel_polynomial_frame_yA A *
    xi_basepoint_scan_residual_kernel_polynomial_frame_residual_quotient A

/-- Rank-one residual kernel obtained from the residual polynomial frame. -/
noncomputable def xi_basepoint_scan_residual_kernel_polynomial_frame_residual_kernel
    (A : Finset ℂ) (x z : ℂ) : ℂ :=
  Polynomial.eval x
      (xi_basepoint_scan_residual_kernel_polynomial_frame_residual_polynomial A) *
    star
      (Polynomial.eval z
        (xi_basepoint_scan_residual_kernel_polynomial_frame_residual_polynomial A))

/-- Unitary change of the one-dimensional residual frame. -/
noncomputable def xi_basepoint_scan_residual_kernel_polynomial_frame_unitary_twist
    (u : ℂ) (A : Finset ℂ) : Polynomial ℂ :=
  C u * xi_basepoint_scan_residual_kernel_polynomial_frame_residual_polynomial A

/-- Paper label: `thm:xi-basepoint-scan-residual-kernel-polynomial-frame`.

The codimension-one leverage-gap package fixes the anchor Gram factorization. In the residual
direction there is a single orthogonal polynomial frame vector, namely `y_A`, so the residual
kernel is rank one, divisible by `y_A`, and unchanged by a unitary scalar change of basis. -/
theorem paper_xi_basepoint_scan_residual_kernel_polynomial_frame {kappa : ℕ}
    (deltas weights : Fin kappa → ℝ) (poles anchors : Fin kappa → ℂ)
    (hweight : ∀ j, weights j = 4 * deltas j)
    (hwt : ∀ j, 0 < weights j)
    (hdet :
      (xi_basepoint_scan_leverage_gap_codim1_closed_form_anchor_data
        deltas weights poles anchors hweight).anchorFrame.det ≠ 0)
    (A : Finset ℂ) (u : ℂ) (hu : u * star u = 1) :
    let D :=
      xi_basepoint_scan_leverage_gap_codim1_closed_form_anchor_data
        deltas weights poles anchors hweight
    let yA := xi_basepoint_scan_residual_kernel_polynomial_frame_yA A
    let pA := xi_basepoint_scan_residual_kernel_polynomial_frame_residual_polynomial A
    D.anchorDetCauchyVandermondeClosedForm ∧
      D.anchorGram.det =
        ((∏ j, ((D.weights j : ℝ) : ℂ)) : ℂ) * D.anchorCauchyMatrix.det ^ (2 : ℕ) ∧
      pA = yA ∧
      (∃ qA, pA = yA * qA) ∧
      (∀ x z,
        xi_basepoint_scan_residual_kernel_polynomial_frame_residual_kernel A x z =
          Polynomial.eval x pA * star (Polynomial.eval z pA)) ∧
      (∀ x z,
        Polynomial.eval x
              (xi_basepoint_scan_residual_kernel_polynomial_frame_unitary_twist u A) *
            star
              (Polynomial.eval z
                (xi_basepoint_scan_residual_kernel_polynomial_frame_unitary_twist u A)) =
          xi_basepoint_scan_residual_kernel_polynomial_frame_residual_kernel A x z) := by
  dsimp
  rcases
      paper_xi_basepoint_scan_leverage_gap_codim1_closed_form
        deltas weights poles anchors hweight hwt hdet with
    ⟨hcv, hgram⟩
  refine ⟨hcv, hgram, ?_, ?_, ?_, ?_⟩
  · simp [xi_basepoint_scan_residual_kernel_polynomial_frame_residual_polynomial,
      xi_basepoint_scan_residual_kernel_polynomial_frame_residual_quotient]
  · refine ⟨xi_basepoint_scan_residual_kernel_polynomial_frame_residual_quotient A, ?_⟩
    simp [xi_basepoint_scan_residual_kernel_polynomial_frame_residual_polynomial]
  · intro x z
    rfl
  · intro x z
    simp [xi_basepoint_scan_residual_kernel_polynomial_frame_unitary_twist,
      xi_basepoint_scan_residual_kernel_polynomial_frame_residual_kernel,
      xi_basepoint_scan_residual_kernel_polynomial_frame_residual_polynomial,
      xi_basepoint_scan_residual_kernel_polynomial_frame_residual_quotient]
    calc
      u * Polynomial.eval x (xi_basepoint_scan_residual_kernel_polynomial_frame_yA A) *
            (star u *
              star
                (Polynomial.eval z
                  (xi_basepoint_scan_residual_kernel_polynomial_frame_yA A))) =
          (u * star u) *
            (Polynomial.eval x
                (xi_basepoint_scan_residual_kernel_polynomial_frame_yA A) *
              star
                (Polynomial.eval z
                  (xi_basepoint_scan_residual_kernel_polynomial_frame_yA A))) := by
            ring
      _ =
          Polynomial.eval x (xi_basepoint_scan_residual_kernel_polynomial_frame_yA A) *
            star
              (Polynomial.eval z
                (xi_basepoint_scan_residual_kernel_polynomial_frame_yA A)) := by
            rw [hu, one_mul]

end Omega.Zeta
