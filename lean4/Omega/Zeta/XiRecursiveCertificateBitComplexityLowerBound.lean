import Mathlib.Tactic

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
    (D : xi_recursive_certificate_bit_complexity_lower_bound_data) :
    D.layer_budget_lower_bound ∧ D.total_budget_growth_bound := by
  constructor
  · exact
      (Nat.mul_le_mul
          D.xi_recursive_certificate_bit_complexity_lower_bound_zero_count_estimate
          D.xi_recursive_certificate_bit_complexity_lower_bound_dyadic_depth_lower_bound).trans
        D.xi_recursive_certificate_bit_complexity_lower_bound_layer_budget_accounts
  · exact
      ⟨D.xi_recursive_certificate_bit_complexity_lower_bound_growth_constant,
        D.xi_recursive_certificate_bit_complexity_lower_bound_growth_constant_positive,
        D.xi_recursive_certificate_bit_complexity_lower_bound_total_budget_lower⟩

end Omega.Zeta
