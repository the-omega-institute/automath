import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.MomentRecurrence
import Omega.OperatorAlgebra.FoldInfoNCEFiniteKMomentFormula

namespace Omega.Folding

open scoped BigOperators

/-- The `K = 2` coefficient in the finite-`K` InfoNCE moment expansion is exactly `log 2`. -/
lemma fold_infonce_k2_collision_recurrence_closure_beta_two :
    Omega.OperatorAlgebra.foldInfoNCEBeta 2 2 = Real.log 2 := by
  unfold Omega.OperatorAlgebra.foldInfoNCEBeta
  rw [show Finset.range 2 = ({0, 1} : Finset ℕ) by decide]
  norm_num

/-- The normalized second collision moment `S₂ / 4^m` obeys the recurrence induced by the
repository's unconditional `S₂` three-step recurrence. -/
lemma fold_infonce_k2_collision_recurrence_closure_normalized_recurrence (m : ℕ) :
    Omega.OperatorAlgebra.foldCollisionMomentNormalized 2 (m + 3) =
      (1 / 2 : ℝ) * Omega.OperatorAlgebra.foldCollisionMomentNormalized 2 (m + 2) +
        (1 / 8 : ℝ) * Omega.OperatorAlgebra.foldCollisionMomentNormalized 2 (m + 1) -
        (1 / 32 : ℝ) * Omega.OperatorAlgebra.foldCollisionMomentNormalized 2 m := by
  have hrec :
      (Omega.momentSum 2 (m + 3) : ℝ) + 2 * Omega.momentSum 2 m =
        2 * Omega.momentSum 2 (m + 2) + 2 * Omega.momentSum 2 (m + 1) := by
    exact_mod_cast Omega.momentSum_two_recurrence m
  have hpow3 : (2 : ℝ) ^ (2 * (m + 3)) = 64 * (2 : ℝ) ^ (2 * m) := by
    rw [show 2 * (m + 3) = 2 * m + 6 by omega, pow_add]
    norm_num
    ring
  have hpow2 : (2 : ℝ) ^ (2 * (m + 2)) = 16 * (2 : ℝ) ^ (2 * m) := by
    rw [show 2 * (m + 2) = 2 * m + 4 by omega, pow_add]
    norm_num
    ring
  have hpow1 : (2 : ℝ) ^ (2 * (m + 1)) = 4 * (2 : ℝ) ^ (2 * m) := by
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
    norm_num
    ring
  have hpow0 : (2 : ℝ) ^ (2 * m) ≠ 0 := by positivity
  unfold Omega.OperatorAlgebra.foldCollisionMomentNormalized
  rw [hpow3, hpow2, hpow1]
  field_simp [hpow0]
  linarith

/-- Paper label: `cor:fold-infonce-k2-collision-recurrence-closure`. For `K = 2`, the finite-`K`
InfoNCE expansion collapses to `(\log 2) c₂(m)`, where `c₂(m)` is the normalized collision
probability, and `c₂` inherits the normalization-corrected three-step recurrence from `S₂`. -/
theorem paper_fold_infonce_k2_collision_recurrence_closure (m : ℕ) :
    Omega.OperatorAlgebra.foldInfoNCEFiniteKMomentExpansion m 2 =
      Real.log 2 * Omega.OperatorAlgebra.foldCollisionMomentNormalized 2 m ∧
    Omega.OperatorAlgebra.foldCollisionMomentNormalized 2 (m + 3) =
      (1 / 2 : ℝ) * Omega.OperatorAlgebra.foldCollisionMomentNormalized 2 (m + 2) +
        (1 / 8 : ℝ) * Omega.OperatorAlgebra.foldCollisionMomentNormalized 2 (m + 1) -
        (1 / 32 : ℝ) * Omega.OperatorAlgebra.foldCollisionMomentNormalized 2 m := by
  refine ⟨?_, fold_infonce_k2_collision_recurrence_closure_normalized_recurrence m⟩
  have hmoment := (Omega.OperatorAlgebra.paper_op_algebra_fold_infonce_finiteK_moment_formula m).1
  simpa [fold_infonce_k2_collision_recurrence_closure_beta_two] using hmoment

end Omega.Folding
