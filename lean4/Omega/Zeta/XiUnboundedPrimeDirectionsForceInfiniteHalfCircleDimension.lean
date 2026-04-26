import Mathlib.Tactic
import Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

namespace Omega.Zeta

open Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

/-- There is no finite host half-circle dimension that bounds every finite prime-support model:
unbounded prime directions force the structural half-circle dimensions to grow without bound. -/
def xi_unbounded_prime_directions_force_infinite_half_circle_dimension_statement : Prop :=
  ¬ ∃ k : ℕ, ∀ N : ℕ, homHalfCircleDim N ≤ (k : ℚ) / 2

/-- Paper label: `cor:xi-unbounded-prime-directions-force-infinite-half-circle-dimension`. -/
theorem paper_xi_unbounded_prime_directions_force_infinite_half_circle_dimension :
    xi_unbounded_prime_directions_force_infinite_half_circle_dimension_statement := by
  rintro ⟨k, hk⟩
  have hkSucc : homHalfCircleDim (k + 1) ≤ (k : ℚ) / 2 := hk (k + 1)
  have hdim :
      homHalfCircleDim (k + 1) = ((k + 1 : ℕ) : ℚ) / 2 :=
    (paper_xi_finite_prime_support_multiplicative_half_circle_dimension (k + 1)).1
  rw [hdim] at hkSucc
  have hle : ((k + 1 : ℕ) : ℚ) ≤ k := by
    linarith
  have hle_nat : k + 1 ≤ k := by
    exact_mod_cast hle
  exact Nat.not_succ_le_self k hle_nat

end Omega.Zeta
