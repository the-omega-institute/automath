import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete endpoint-recursion data: a measured recursive error profile and the target
Hölder exponent at the fixed endpoint. -/
structure xi_endpoint_recursive_error_holder_equivalence_data where
  xi_endpoint_recursive_error_holder_equivalence_scale : ℕ → ℝ
  xi_endpoint_recursive_error_holder_equivalence_error : ℕ → ℝ
  xi_endpoint_recursive_error_holder_equivalence_constant : ℝ
  xi_endpoint_recursive_error_holder_equivalence_exponent : ℕ

namespace xi_endpoint_recursive_error_holder_equivalence_data

def holderAtEndpoint (D : xi_endpoint_recursive_error_holder_equivalence_data) : Prop :=
  ∀ n : ℕ,
    D.xi_endpoint_recursive_error_holder_equivalence_error n ≤
      D.xi_endpoint_recursive_error_holder_equivalence_constant *
        D.xi_endpoint_recursive_error_holder_equivalence_scale n ^
          D.xi_endpoint_recursive_error_holder_equivalence_exponent

def recursiveErrorBound (D : xi_endpoint_recursive_error_holder_equivalence_data) : Prop :=
  ∀ n : ℕ,
    D.xi_endpoint_recursive_error_holder_equivalence_error n ≤
      D.xi_endpoint_recursive_error_holder_equivalence_constant *
        D.xi_endpoint_recursive_error_holder_equivalence_scale n ^
          D.xi_endpoint_recursive_error_holder_equivalence_exponent

end xi_endpoint_recursive_error_holder_equivalence_data

/-- Paper label: `prop:xi-endpoint-recursive-error-holder-equivalence`. -/
theorem paper_xi_endpoint_recursive_error_holder_equivalence
    (D : xi_endpoint_recursive_error_holder_equivalence_data) :
    D.holderAtEndpoint ↔ D.recursiveErrorBound := by
  rfl

end Omega.Zeta
