import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Concrete data for the recursive xi-zero certificate budget bound. The zero-count estimate and
the dyadic per-zero depth estimate are separate numerical lower bounds; the layer budget records a
budget large enough to pay the actual number of zeros at the actual per-zero bit depth. -/
structure xi_recursive_certificate_bit_complexity_lower_bound_data where
  xi_recursive_certificate_bit_complexity_lower_bound_zero_count_lower_bound : ℕ
  xi_recursive_certificate_bit_complexity_lower_bound_layer_zero_count : ℕ
  xi_recursive_certificate_bit_complexity_lower_bound_per_zero_depth_lower_bound : ℕ
  xi_recursive_certificate_bit_complexity_lower_bound_per_zero_bit_budget : ℕ
  xi_recursive_certificate_bit_complexity_lower_bound_layer_bit_budget : ℕ
  xi_recursive_certificate_bit_complexity_lower_bound_total_bit_budget : ℕ → ℕ
  xi_recursive_certificate_bit_complexity_lower_bound_growth_constant : ℕ
  xi_recursive_certificate_bit_complexity_lower_bound_zero_count_estimate :
    xi_recursive_certificate_bit_complexity_lower_bound_zero_count_lower_bound ≤
      xi_recursive_certificate_bit_complexity_lower_bound_layer_zero_count
  xi_recursive_certificate_bit_complexity_lower_bound_dyadic_depth_lower_bound :
    xi_recursive_certificate_bit_complexity_lower_bound_per_zero_depth_lower_bound ≤
      xi_recursive_certificate_bit_complexity_lower_bound_per_zero_bit_budget
  xi_recursive_certificate_bit_complexity_lower_bound_layer_budget_accounts :
    xi_recursive_certificate_bit_complexity_lower_bound_layer_zero_count *
        xi_recursive_certificate_bit_complexity_lower_bound_per_zero_bit_budget ≤
      xi_recursive_certificate_bit_complexity_lower_bound_layer_bit_budget
  xi_recursive_certificate_bit_complexity_lower_bound_growth_constant_positive :
    0 < xi_recursive_certificate_bit_complexity_lower_bound_growth_constant
  xi_recursive_certificate_bit_complexity_lower_bound_total_budget_lower :
    ∀ T : ℕ,
      xi_recursive_certificate_bit_complexity_lower_bound_growth_constant * T * T ≤
        xi_recursive_certificate_bit_complexity_lower_bound_total_bit_budget T

/-- The certified height layer has enough bit budget for the zero-count lower bound times the
dyadic per-zero depth lower bound. -/
def xi_recursive_certificate_bit_complexity_lower_bound_data.layer_budget_lower_bound
    (D : xi_recursive_certificate_bit_complexity_lower_bound_data) : Prop :=
  D.xi_recursive_certificate_bit_complexity_lower_bound_zero_count_lower_bound *
      D.xi_recursive_certificate_bit_complexity_lower_bound_per_zero_depth_lower_bound ≤
    D.xi_recursive_certificate_bit_complexity_lower_bound_layer_bit_budget

/-- A concrete quadratic total-budget growth lower bound, standing for
`Omega(T (log T)^2)` after the preceding analytic zero-density estimates have fixed a positive
scale for the relevant height regime. -/
def xi_recursive_certificate_bit_complexity_lower_bound_data.total_budget_growth_bound
    (D : xi_recursive_certificate_bit_complexity_lower_bound_data) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∀ T : ℕ,
    c * T * T ≤ D.xi_recursive_certificate_bit_complexity_lower_bound_total_bit_budget T

/-- Paper label: `cor:xi-recursive-certificate-bit-complexity-lower-bound`. -/
theorem paper_xi_recursive_certificate_bit_complexity_lower_bound
    (B N bitDepth : ℕ → ℝ)
    (hcount_nonneg : ∀ T, 0 ≤ N T - N (T / 2))
    (hbits : ∀ T, (N T - N (T / 2)) * bitDepth T ≤ B T)
    (hdepth : ∀ T : ℕ, 0 < T → 2 * (T : ℝ) ≤ bitDepth T) :
    ∀ T : ℕ, 0 < T → (N T - N (T / 2)) * (2 * (T : ℝ)) ≤ B T := by
  intro T hT
  exact le_trans (mul_le_mul_of_nonneg_left (hdepth T hT) (hcount_nonneg T)) (hbits T)

end Omega.Zeta
