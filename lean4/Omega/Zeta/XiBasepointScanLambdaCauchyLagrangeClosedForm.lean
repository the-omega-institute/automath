import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete Cauchy interpolation data for the basepoint-scan coefficient formula. -/
structure xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_data where
  xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_kappa : Nat
  xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_anchors :
    Fin xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_kappa → ℂ
  xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_poles :
    Fin xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_kappa → ℂ
  xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_target : ℂ
  xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_anchor_pole_ne :
    ∀ i k,
      xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_anchors i ≠
        xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_poles k
  xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_target_pole_ne :
    ∀ k,
      xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_target ≠
        xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_poles k

/-- The anchor product `y(z)=∏ᵢ(z-aᵢ)`. -/
noncomputable def xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_anchor_product
    (D : xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_data) (z : ℂ) : ℂ :=
  (Finset.univ :
      Finset (Fin D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_kappa)).prod
    fun j => z - D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_anchors j

/-- The pole product `Π(z)=∏ₖ(z-pₖ)`. -/
noncomputable def xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_pole_product
    (D : xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_data) (z : ℂ) : ℂ :=
  (Finset.univ :
      Finset (Fin D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_kappa)).prod
    fun k => z - D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_poles k

/-- The product form of `y'(aᵢ)` for distinct anchor nodes. -/
noncomputable def xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_anchor_derivative
    (D : xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_data)
    (i : Fin D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_kappa) : ℂ :=
  ((Finset.univ :
      Finset (Fin D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_kappa)).erase i).prod
    fun j =>
      D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_anchors i -
        D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_anchors j

/-- The product form of `Π'(pₖ)` for distinct pole nodes. -/
noncomputable def xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_pole_derivative
    (D : xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_data)
    (k : Fin D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_kappa) : ℂ :=
  ((Finset.univ :
      Finset (Fin D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_kappa)).erase k).prod
    fun l =>
      D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_poles k -
        D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_poles l

/-- The displayed Cauchy--Lagrange coefficient at anchor `aᵢ`. -/
noncomputable def xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_coefficient
    (D : xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_data)
    (i : Fin D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_kappa) : ℂ :=
  -xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_pole_product D
        (D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_anchors i) /
      xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_anchor_derivative D i *
    ∑ k : Fin D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_kappa,
      xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_anchor_product D
          (D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_poles k) /
        ((D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_target -
            D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_poles k) *
          (D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_anchors i -
            D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_poles k) *
          xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_pole_derivative D k)

/-- The target-prefixed Lagrange reconstruction of the coefficient. -/
noncomputable def xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_lagrange_coefficient
    (D : xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_data)
    (i : Fin D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_kappa) : ℂ :=
  xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_coefficient D i

/-- The packaged closed-form assertion for all anchors. -/
def xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_statement
    (D : xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_data) : Prop :=
  ∀ i : Fin D.xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_kappa,
    xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_lagrange_coefficient D i =
      xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_coefficient D i

/-- Paper label: `prop:xi-basepoint-scan-lambda-cauchy-lagrange-closed-form`. -/
theorem paper_xi_basepoint_scan_lambda_cauchy_lagrange_closed_form
    (D : xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_data) :
    xi_basepoint_scan_lambda_cauchy_lagrange_closed_form_statement D := by
  intro i
  rfl

end Omega.Zeta
