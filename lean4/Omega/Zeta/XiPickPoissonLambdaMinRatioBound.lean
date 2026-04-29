import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The top Pick--Poisson coefficient, represented as the product of the positive eigenvalues. -/
noncomputable def xi_pick_poisson_lambda_min_ratio_bound_top {kappa : ℕ}
    (lambda : Fin kappa → ℝ) : ℝ :=
  ∏ i, lambda i

/-- The previous Pick--Poisson coefficient, represented as the sum of complementary products. -/
noncomputable def xi_pick_poisson_lambda_min_ratio_bound_previous {kappa : ℕ}
    (lambda : Fin kappa → ℝ) : ℝ :=
  Finset.univ.sum fun j => (Finset.univ.erase j).prod lambda

/-- Paper label: `cor:xi-pick-poisson-lambda-min-ratio-bound`.

For a finite positive eigenvalue list, the ratio of the full product to the sum of
complementary products is bounded above by the minimum eigenvalue. -/
theorem paper_xi_pick_poisson_lambda_min_ratio_bound {kappa : ℕ}
    (lambda : Fin kappa → ℝ) (lambdaMin : ℝ)
    (hpos : ∀ i, 0 < lambda i)
    (hMinAttained : ∃ i, lambdaMin = lambda i) :
    xi_pick_poisson_lambda_min_ratio_bound_top lambda /
        xi_pick_poisson_lambda_min_ratio_bound_previous lambda ≤ lambdaMin := by
  classical
  obtain ⟨i0, hMin⟩ := hMinAttained
  let complement : ℝ := (Finset.univ.erase i0).prod lambda
  have hComplement_pos : 0 < complement := by
    exact Finset.prod_pos fun i _ => hpos i
  have hComplement_nonneg : 0 ≤ complement := le_of_lt hComplement_pos
  have hDen_ge :
      complement ≤ xi_pick_poisson_lambda_min_ratio_bound_previous lambda := by
    dsimp [complement, xi_pick_poisson_lambda_min_ratio_bound_previous]
    exact Finset.single_le_sum
      (fun j _ => Finset.prod_nonneg fun i _ => le_of_lt (hpos i)) (Finset.mem_univ i0)
  have hDen_pos : 0 < xi_pick_poisson_lambda_min_ratio_bound_previous lambda :=
    lt_of_lt_of_le hComplement_pos hDen_ge
  have hTop_split :
      xi_pick_poisson_lambda_min_ratio_bound_top lambda = lambda i0 * complement := by
    dsimp [xi_pick_poisson_lambda_min_ratio_bound_top, complement]
    calc
      Finset.univ.prod lambda = (insert i0 (Finset.univ.erase i0)).prod lambda := by
        rw [Finset.insert_erase (Finset.mem_univ i0)]
      _ = lambda i0 * (Finset.univ.erase i0).prod lambda := by
        rw [Finset.prod_insert]
        simp
  have hTop_le :
      xi_pick_poisson_lambda_min_ratio_bound_top lambda ≤
        lambdaMin * xi_pick_poisson_lambda_min_ratio_bound_previous lambda := by
    rw [hTop_split, hMin]
    exact mul_le_mul_of_nonneg_left hDen_ge (le_of_lt (hpos i0))
  exact (div_le_iff₀ hDen_pos).2 hTop_le

end Omega.Zeta
