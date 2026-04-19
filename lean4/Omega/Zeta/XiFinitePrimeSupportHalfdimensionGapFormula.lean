import Mathlib.Tactic
import Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

namespace Omega.Zeta

open Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

/-- The structural and implementation half-circle dimensions for finite prime support differ by
exactly `((r : ℚ) - 1) / 2`, so equality occurs precisely in rank `1`.
    thm:xi-finite-prime-support-halfdimension-gap-formula -/
theorem paper_xi_finite_prime_support_halfdimension_gap_formula (r : ℕ) :
    homHalfCircleDim r = (r : ℚ) / 2 ∧
      implHalfCircleDim = (1 : ℚ) / 2 ∧
      homHalfCircleDim r - implHalfCircleDim = ((r : ℚ) - 1) / 2 ∧
      (homHalfCircleDim r = implHalfCircleDim ↔ r = 1) := by
  rcases paper_xi_finite_prime_support_multiplicative_half_circle_dimension r with
    ⟨hHom, hImpl, hGap⟩
  refine ⟨hHom, hImpl, hGap, ?_⟩
  rw [hHom, hImpl]
  constructor
  · intro hEq
    have hRat : (r : ℚ) = 1 := by
      linarith
    exact_mod_cast hRat
  · intro hr
    subst hr
    norm_num

end Omega.Zeta
