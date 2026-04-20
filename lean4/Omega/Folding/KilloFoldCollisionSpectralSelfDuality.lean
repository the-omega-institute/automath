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

end Omega.Folding
