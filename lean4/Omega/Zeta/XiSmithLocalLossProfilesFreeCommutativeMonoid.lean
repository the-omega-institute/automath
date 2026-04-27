import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The Smith local-loss profile records each finitely supported exponent coefficient. -/
def xi_smith_local_loss_profiles_free_commutative_monoid_profile
    (c : ℕ →₀ ℕ) : ℕ → ℕ :=
  fun k => c k

/-- Paper label: `thm:xi-smith-local-loss-profiles-free-commutative-monoid`. -/
theorem paper_xi_smith_local_loss_profiles_free_commutative_monoid :
    Function.Injective
      (xi_smith_local_loss_profiles_free_commutative_monoid_profile : (ℕ →₀ ℕ) → ℕ → ℕ) := by
  intro c d h
  ext k
  exact congrFun h k

end Omega.Zeta
