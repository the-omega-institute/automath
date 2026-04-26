import Mathlib.Tactic
import Omega.Folding.CollisionKernel

namespace Omega.Folding

/-- Expanding the `A_4(t)` characteristic polynomial at `lambda` and `-lambda` cancels the
odd-power and `t`-dependent terms, leaving the even self-dual part.
`thm:killo-fold-collision-spectral-self-duality` -/
theorem paper_killo_fold_collision_spectral_self_duality (t : ℤ) («λ» : ℤ) :
    («λ» ^ 5 - 2 * «λ» ^ 4 - t * «λ» ^ 3 - 2 * «λ» + 2) +
        ((-«λ») ^ 5 - 2 * (-«λ») ^ 4 - t * (-«λ») ^ 3 - 2 * (-«λ») + 2) =
      4 * (1 - «λ» ^ 4) := by
  simpa [charPolyA4t] using charPolyA4t_selfduality t «λ»

/-- Paper label: `cor:killo-fold-collision-self-dual-zeros`. -/
theorem paper_killo_fold_collision_self_dual_zeros
    (t : ℤ) («λ0» : ℤ)
    (hroot : «λ0» ^ 5 - 2 * «λ0» ^ 4 - t * «λ0» ^ 3 - 2 * «λ0» + 2 = 0) :
    ((-«λ0») ^ 5 - 2 * (-«λ0») ^ 4 - t * (-«λ0») ^ 3 - 2 * (-«λ0») + 2 = 0) ↔
      «λ0» ^ 4 = 1 := by
  have hself := paper_killo_fold_collision_spectral_self_duality t «λ0»
  constructor
  · intro hneg
    have hfour : 4 * (1 - «λ0» ^ 4) = 0 := by
      linarith
    have hone : 1 - «λ0» ^ 4 = 0 := by
      nlinarith
    linarith
  · intro hpow
    have hfour : 4 * (1 - «λ0» ^ 4) = 0 := by
      nlinarith
    linarith

end Omega.Folding
