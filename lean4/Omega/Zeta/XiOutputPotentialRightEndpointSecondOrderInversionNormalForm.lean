import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The substitution `x = exp (-θ / 2)` used at the right endpoint. -/
def xi_output_potential_right_endpoint_second_order_inversion_normal_form_substitution
    (θ : ℝ) : ℝ :=
  Real.exp (-θ / 2)

/-- The second-order inversion normal form for the dual parameter `θ(1/2 - δ)`. -/
def xi_output_potential_right_endpoint_second_order_inversion_normal_form_theta
    (c d e δ : ℝ) : ℝ :=
  2 * Real.log (d / (2 * c * δ)) + ((8 * c * e) / d ^ 2 - 4) * δ

/-- The corresponding second-order normal form for the rate function. -/
def xi_output_potential_right_endpoint_second_order_inversion_normal_form_rate
    (lam c d e δ : ℝ) : ℝ :=
  Real.log (lam / c) - 2 * δ * Real.log (d / (2 * c * δ)) - 2 * δ +
    (2 - (4 * c * e) / d ^ 2) * δ ^ 2

/-- Paper label:
`thm:xi-output-potential-right-endpoint-second-order-inversion-normal-form`.
After substituting `a = d / c` and `b = e / c - d² / (2 c²)`, the standard quadratic inversion
coefficients rewrite to the explicit `(c,d,e)` normal forms for both `θ` and the rate function. -/
def xi_output_potential_right_endpoint_second_order_inversion_normal_form_statement : Prop :=
  ∀ lam c d e a b δ : ℝ,
    c ≠ 0 →
    d ≠ 0 →
    0 < δ →
    a = d / c →
    b = e / c - d ^ 2 / (2 * c ^ 2) →
      2 * Real.log (a / (2 * δ)) + (8 * b / a ^ 2) * δ =
          xi_output_potential_right_endpoint_second_order_inversion_normal_form_theta c d e δ ∧
        Real.log (lam / c) - 2 * δ * Real.log (a / (2 * δ)) - 2 * δ -
            (4 * b / a ^ 2) * δ ^ 2 =
          xi_output_potential_right_endpoint_second_order_inversion_normal_form_rate
            lam c d e δ

theorem paper_xi_output_potential_right_endpoint_second_order_inversion_normal_form :
    xi_output_potential_right_endpoint_second_order_inversion_normal_form_statement := by
  intro lam c d e a b δ hc0 hd0 hδ ha hb
  subst a b
  constructor
  · unfold xi_output_potential_right_endpoint_second_order_inversion_normal_form_theta
    have hlog :
        (d / c) / (2 * δ) = d / (2 * c * δ) := by
      field_simp [hc0, hδ.ne']
    have hcoeff :
        8 * (e / c - d ^ 2 / (2 * c ^ 2)) / (d / c) ^ 2 = (8 * c * e) / d ^ 2 - 4 := by
      field_simp [hc0, hd0]
      ring
    rw [hlog, hcoeff]
  · unfold xi_output_potential_right_endpoint_second_order_inversion_normal_form_rate
    have hlog :
        (d / c) / (2 * δ) = d / (2 * c * δ) := by
      field_simp [hc0, hδ.ne']
    have hcoeff :
        4 * (e / c - d ^ 2 / (2 * c ^ 2)) / (d / c) ^ 2 = (4 * c * e) / d ^ 2 - 2 := by
      field_simp [hc0, hd0]
      ring
    rw [hlog, hcoeff]
    ring

end

end Omega.Zeta
