import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import Omega.Folding.BayesKinkGeometry

noncomputable section

namespace Omega.Folding

/-- The Bernoulli-`p` mismatch-density cubic has a unique root in `(0, 1)`, and at that root the
closed-form density collapses to `p^2`. -/
theorem paper_fold_gauge_anomaly_bernoulli_p_density_unimodal :
    ∃! pStar : ℝ, pStar ∈ Set.Ioo 0 1 ∧ pStar ^ 3 + 2 * pStar - 2 = 0 ∧
      pStar ^ 2 * (3 - 2 * pStar) / (1 + pStar ^ 3) = pStar ^ 2 := by
  let f : ℝ → ℝ := fun p => p ^ 3 + 2 * p - 2
  have hf_cont : Continuous f := by
    simpa [f] using
      (((continuous_id.pow 3).add (continuous_const.mul continuous_id)).sub continuous_const)
  have hzero_mem : (0 : ℝ) ∈ Set.Ioo (f 0) (f 1) := by
    dsimp [f]
    norm_num
  rcases intermediate_value_Ioo (show (0 : ℝ) ≤ 1 by norm_num) hf_cont.continuousOn hzero_mem with
    ⟨pStar, hpStar, hpRoot⟩
  refine ⟨pStar, ?_, ?_⟩
  · refine ⟨hpStar, hpRoot, ?_⟩
    have hden : 1 + pStar ^ 3 = 3 - 2 * pStar := by
      linarith
    have hden_ne : 3 - 2 * pStar ≠ 0 := by
      intro hzero
      have hpow_pos : 0 < pStar ^ 3 := by
        exact pow_pos hpStar.1 3
      rw [← hden] at hzero
      nlinarith
    rw [hden, div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hden_ne, mul_one]
  · intro q hq
    rcases hq with ⟨hqIoo, hqRoot, _⟩
    have hf_strict : StrictMonoOn f (Set.Icc (0 : ℝ) 1) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1) ?_ ?_
      · exact hf_cont.continuousOn
      · intro x hx
        have hderiv : deriv f x = 3 * x ^ 2 + 2 := by
          simpa [f, add_assoc, add_left_comm, add_comm, sub_eq_add_neg, mul_comm, mul_left_comm,
            mul_assoc] using
            (show deriv (fun x : ℝ => x ^ (3 : ℕ) + 2 * x - 2) x = (3 : ℝ) * x ^ 2 + 2 by
              simp)
        rw [hderiv]
        nlinarith [sq_nonneg x]
    exact
      (hf_strict.injOn ⟨le_of_lt hpStar.1, le_of_lt hpStar.2⟩
        ⟨le_of_lt hqIoo.1, le_of_lt hqIoo.2⟩ (hpRoot.trans hqRoot.symm)).symm

/-- Paper label: `cor:fold-gauge-anomaly-bernoulli-p-density-maximizer-cardano`. -/
theorem paper_fold_gauge_anomaly_bernoulli_p_density_maximizer_cardano :
    ∃! pStar : Real, pStar ∈ Set.Ioo 0 1 ∧ pStar ^ 3 + 2 * pStar - 2 = 0 ∧
      pStar ^ 2 * (3 - 2 * pStar) / (1 + pStar ^ 3) = pStar ^ 2 := by
  exact paper_fold_gauge_anomaly_bernoulli_p_density_unimodal

end Omega.Folding
