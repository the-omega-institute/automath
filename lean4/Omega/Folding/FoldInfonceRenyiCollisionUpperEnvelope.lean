import Mathlib.Data.Real.Basic
import Omega.Folding.FoldInfoNCEBayesInfoncePowerSumExpansion
import Omega.Folding.MomentRecurrence

namespace Omega.Folding

private lemma fold_infonce_renyi_collision_upper_envelope_normalized_le_one
    (m q : ℕ) (hq : 1 ≤ q) :
    Omega.OperatorAlgebra.foldCollisionMomentNormalized q m ≤ 1 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hq
  unfold Omega.OperatorAlgebra.foldCollisionMomentNormalized
  have hsum_nat : Omega.momentSum (t + 1) m ≤ (2 ^ m) ^ (t + 1) := by
    calc
      Omega.momentSum (t + 1) m ≤ Omega.X.maxFiberMultiplicity m ^ t * 2 ^ m := by
        simpa using Omega.momentSum_le_max_pow (t + 1) m (Nat.succ_le_succ (Nat.zero_le t))
      _ ≤ (2 ^ m) ^ t * 2 ^ m := by
        exact Nat.mul_le_mul_right (2 ^ m) (Nat.pow_le_pow_left (Omega.maxFiberMultiplicity_le_pow m) t)
      _ = (2 ^ m) ^ (t + 1) := by
        symm
        exact pow_succ (2 ^ m) t
  have hsum_nat' : Omega.momentSum (t + 1) m ≤ 2 ^ ((t + 1) * m) := by
    calc
      Omega.momentSum (t + 1) m ≤ (2 ^ m) ^ (t + 1) := hsum_nat
      _ = 2 ^ (m * (t + 1)) := by rw [← pow_mul]
      _ = 2 ^ ((t + 1) * m) := by rw [Nat.mul_comm]
  have hsum_real : (Omega.momentSum (t + 1) m : ℝ) ≤ (2 : ℝ) ^ ((t + 1) * m) := by
    exact_mod_cast hsum_nat'
  have hden_pos : 0 < (2 : ℝ) ^ ((t + 1) * m) := by positivity
  have hdiv :
      (Omega.momentSum (t + 1) m : ℝ) / (2 : ℝ) ^ ((t + 1) * m) ≤ 1 := by
    have hdiv' :
        (Omega.momentSum (t + 1) m : ℝ) / (2 : ℝ) ^ ((t + 1) * m) ≤
          ((2 : ℝ) ^ ((t + 1) * m)) / (2 : ℝ) ^ ((t + 1) * m) := by
      exact div_le_div_of_nonneg_right hsum_real (by positivity)
    simpa [hden_pos.ne'] using hdiv'
  simpa [Nat.add_comm] using hdiv

/-- Paper label: `thm:fold-infonce-renyi-collision-upper-envelope`.
The Bayes-optimal finite-`K` InfoNCE loss expands against the normalized collision moments, the
first normalized moment is exactly `1`, and every higher normalized collision moment is bounded
above by the uniform envelope `1`. -/
theorem paper_fold_infonce_renyi_collision_upper_envelope (m K : Nat) :
    Omega.OperatorAlgebra.foldInfoNCEFiniteKMomentExpansion m K =
      Finset.sum (Finset.Icc 2 K) (fun r =>
        (Nat.choose (K - 1) (r - 1) : Real) *
          (((-1 : Real) ^ r) * Omega.Folding.foldInfoNCEAlpha (r - 1)) *
            Omega.OperatorAlgebra.foldCollisionMomentNormalized r m) ∧
      Omega.OperatorAlgebra.foldCollisionMomentNormalized 1 m = 1 ∧
      (∀ q, 1 ≤ q → Omega.OperatorAlgebra.foldCollisionMomentNormalized q m ≤ 1) := by
  refine ⟨paper_fold_infonce_bayes_infonce_power_sum_expansion m K, ?_, ?_⟩
  · unfold Omega.OperatorAlgebra.foldCollisionMomentNormalized
    rw [Omega.momentSum_one]
    simp
  · intro q hq
    exact fold_infonce_renyi_collision_upper_envelope_normalized_le_one m q hq

end Omega.Folding
