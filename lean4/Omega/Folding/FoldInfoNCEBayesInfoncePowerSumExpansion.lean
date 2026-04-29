import Mathlib.Tactic
import Omega.Folding.FoldInfoNCEAlphaLogClosedForm
import Omega.OperatorAlgebra.FoldInfoNCELaplaceRenyiMomentExpansion

namespace Omega.Folding

open scoped BigOperators
noncomputable section

private lemma neg_one_pow_add_two (n : ℕ) : (-1 : ℝ) ^ (n + 2) = (-1 : ℝ) ^ n := by
  rw [pow_add]
  norm_num

/-- Paper label: `prop:fold-infonce-bayes-infonce-power-sum-expansion`. -/
theorem paper_fold_infonce_bayes_infonce_power_sum_expansion (m K : Nat) :
    Omega.OperatorAlgebra.foldInfoNCEFiniteKMomentExpansion m K =
      Finset.sum (Finset.Icc 2 K) (fun r =>
        (Nat.choose (K - 1) (r - 1) : Real) *
          (((-1 : Real) ^ r) * Omega.Folding.foldInfoNCEAlpha (r - 1)) *
            Omega.OperatorAlgebra.foldCollisionMomentNormalized r m) := by
  rw [Omega.OperatorAlgebra.paper_fold_infonce_laplace_renyi_moment_expansion]
  dsimp
  have hIcc :
      Finset.Icc 2 K = (Finset.Icc 1 (K - 1)).map ⟨Nat.succ, by
        intro a b h
        exact Nat.succ.inj h⟩ := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro hq
      refine ⟨q - 1, ?_, by omega⟩
      omega
    · intro hq
      rcases hq with ⟨a, ha, rfl⟩
      omega
  rw [hIcc, Finset.sum_map]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj1)
  change
      (((-1 : ℝ) ^ t * (Nat.choose (K - 1) t.succ : ℝ) *
          -∑ k ∈ Finset.range (t.succ + 1),
            (-1 : ℝ) ^ k * (Nat.choose t.succ k : ℝ) * Real.log (k + 1)) *
        Omega.OperatorAlgebra.foldCollisionMomentNormalized (t.succ + 1) m) =
        (Nat.choose (K - 1) t.succ : ℝ) *
          (((-1 : ℝ) ^ (t.succ + 1)) * Omega.Folding.foldInfoNCEAlpha t.succ) *
            Omega.OperatorAlgebra.foldCollisionMomentNormalized (t.succ + 1) m
  rw [← Omega.Folding.paper_fold_infonce_alpha_log_closed_form t.succ]
  have hpow : (-1 : ℝ) ^ (t.succ + 1) = (-1 : ℝ) ^ t := by
    simpa [Nat.succ_eq_add_one, add_assoc] using neg_one_pow_add_two t
  rw [hpow]
  ring

end
end Omega.Folding
