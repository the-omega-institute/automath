import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Polynomial

/-- Concrete polynomial data for the Chebyshev--Dwork congruence chain in the invariant
coordinate `t = u + u⁻¹`. The Laurent side has already been reduced to the even-palindrome
representatives `P₀, P₁, P₂`, and the only remaining rewrite is the quadratic identity
`u² + u⁻² = t² - 2`. -/
structure ChebyshevDworkCongruenceChainData where
  t : Polynomial ℤ
  uSqPlusInvSq : Polynomial ℤ
  U₀ : Polynomial ℤ
  U₁ : Polynomial ℤ
  U₂ : Polynomial ℤ
  P₀ : Polynomial ℤ
  P₁ : Polynomial ℤ
  P₂ : Polynomial ℤ
  evenPalindrome₀ : U₀ = P₀
  evenPalindrome₁ : U₁ = P₁
  evenPalindrome₂ : U₂ = P₂
  chebyshevCoordinate : uSqPlusInvSq = t ^ 2 - C 2
  dworkCongruence : U₂ = (uSqPlusInvSq + C 2) * U₁ - U₀

/-- The closed recurrence in `ℤ[t]` obtained from the Laurent-side Dwork congruence after
rewriting through `u² + u⁻² = t² - 2` and cancelling the common `u`-power. -/
def ChebyshevDworkCongruenceChainData.closedCongruenceRecurrence
    (D : ChebyshevDworkCongruenceChainData) : Prop :=
  D.P₂ = D.t ^ 2 * D.P₁ - D.P₀

/-- Paper-facing Chebyshev--Dwork congruence chain: the even-palindrome invariant descends the
Laurent-side Dwork congruence to a closed recurrence in `ℤ[t]`.
    thm:chebyshev-dwork-congruence-chain -/
theorem paper_chebyshev_dwork_congruence_chain (D : ChebyshevDworkCongruenceChainData) :
    D.closedCongruenceRecurrence := by
  dsimp [ChebyshevDworkCongruenceChainData.closedCongruenceRecurrence]
  calc
    D.P₂ = D.U₂ := D.evenPalindrome₂.symm
    _ = (D.uSqPlusInvSq + C 2) * D.U₁ - D.U₀ := D.dworkCongruence
    _ = ((D.t ^ 2 - C 2) + C 2) * D.U₁ - D.U₀ := by rw [D.chebyshevCoordinate]
    _ = D.t ^ 2 * D.U₁ - D.U₀ := by ring
    _ = D.t ^ 2 * D.P₁ - D.P₀ := by rw [D.evenPalindrome₁, D.evenPalindrome₀]

end Omega.SyncKernelWeighted
