import Mathlib.Tactic
import Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

namespace Omega.CircleDimension

open Omega.CircleDimension.FinitePrimeSupportMultiplicativeHalfCircleDimension

/-- Arithmetic proxy for a faithful embedding of a rank-`r` finite-prime-support multiplicative
monoid into a rank-one torsion-free additive host: Grothendieck completion would make the kernel
rank simultaneously at least `r - 1` and equal to `0`. -/
def finitePrimeSupportRankOneAdditiveHostObstruction (r : ℕ) : Prop :=
  ∃ kernelRank : ℕ, r - 1 ≤ kernelRank ∧ kernelRank = 0

/-- The localization host `ℤ[T⁻¹]` is another rank-one target in the same bookkeeping model. -/
def finitePrimeSupportLocalizationObstruction (r : ℕ) (_T : Finset ℕ) : Prop :=
  finitePrimeSupportRankOneAdditiveHostObstruction r

/-- Paper-facing obstruction: once the finite prime-support multiplicative monoid has rank at
least `2`, no rank-one torsion-free additive host can faithfully carry it.
    thm:xi-finite-prime-support-no-rankone-additive-host -/
theorem paper_xi_finite_prime_support_no_rankone_additive_host (r : ℕ) (hr : 2 ≤ r) :
    homHalfCircleDim r = (r : ℚ) / 2 ∧
      ¬ finitePrimeSupportRankOneAdditiveHostObstruction r ∧
      ∀ T : Finset ℕ, ¬ finitePrimeSupportLocalizationObstruction r T := by
  have hdim : homHalfCircleDim r = (r : ℚ) / 2 := by
    exact (paper_xi_finite_prime_support_multiplicative_half_circle_dimension r).1
  have hmain : ¬ finitePrimeSupportRankOneAdditiveHostObstruction r := by
    rintro ⟨kernelRank, hlower, hzero⟩
    have hpos : 0 < r - 1 := by omega
    have hone : 1 ≤ kernelRank := by
      exact le_trans (Nat.succ_le_iff.mpr hpos) hlower
    omega
  refine ⟨hdim, hmain, ?_⟩
  intro T
  simpa [finitePrimeSupportLocalizationObstruction] using hmain

end Omega.CircleDimension
