import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-multiplicative-ray-finite-plateau-rigidity`.
If the finite telescoping loss along a multiplicative ray is a sum of nonnegative terms and
the plateau makes that sum vanish, then every layer loss in the finite ray segment vanishes. -/
theorem paper_conclusion_multiplicative_ray_finite_plateau_rigidity
    (N : ℕ) (loss : Fin N → ℝ)
    (conclusion_multiplicative_ray_finite_plateau_rigidity_loss_nonneg :
      ∀ k, 0 ≤ loss k)
    (conclusion_multiplicative_ray_finite_plateau_rigidity_plateau :
      (∑ k : Fin N, loss k) = 0) :
    ∀ k : Fin N, loss k = 0 := by
  intro k
  exact
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => conclusion_multiplicative_ray_finite_plateau_rigidity_loss_nonneg j)).mp
      conclusion_multiplicative_ray_finite_plateau_rigidity_plateau k (by simp)

end Omega.Conclusion
