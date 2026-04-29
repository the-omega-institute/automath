import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.FiberArithmeticProperties
import Omega.Folding.FoldInfoNCEEntropyDegenerationSecondOrder

namespace Omega.Folding

noncomputable section

/-- Exponential negative-sample schedule `K_m = ⌈e^{γ m}⌉`. -/
def fold_infonce_exponential_k_stable_expansion_schedule (γ : ℝ) (m : ℕ) : ℕ :=
  Nat.ceil (Real.exp (γ * m))

/-- The normalized large-`K` InfoNCE quantity evaluated on the exponential schedule. -/
def fold_infonce_exponential_k_stable_expansion_normalized_gap (γ : ℝ) (m : ℕ) : ℝ :=
  (Real.log (fold_infonce_exponential_k_stable_expansion_schedule γ m : ℝ) -
      Omega.OperatorAlgebra.foldInfoNCELossInfimum m
        (fold_infonce_exponential_k_stable_expansion_schedule γ m)) / m

private lemma fold_infonce_exponential_k_stable_expansion_schedule_ge_two
    {γ : ℝ} (hγ : 0 < γ) {m : ℕ} (hm : 1 ≤ m) :
    2 ≤ fold_infonce_exponential_k_stable_expansion_schedule γ m := by
  unfold fold_infonce_exponential_k_stable_expansion_schedule
  have hm_real_pos : 0 < (m : ℝ) := by
    exact_mod_cast hm
  have hγm_pos : 0 < γ * m := by
    exact mul_pos hγ hm_real_pos
  have hexp_gt_one : (1 : ℝ) < Real.exp (γ * m) := by
    simpa using Real.one_lt_exp_iff.mpr hγm_pos
  have hceil_gt_one : (1 : ℕ) < Nat.ceil (Real.exp (γ * m)) := by
    exact (Nat.lt_ceil).2 (by simpa using hexp_gt_one)
  exact Nat.succ_le_of_lt hceil_gt_one

/-- Paper label: `cor:fold-infonce-exponential-K-stable-expansion`.
For the exponential schedule `K_m = ⌈e^{γ m}⌉` with `γ > 0`, the finite-`K` InfoNCE optimum is
already on the stable branch for every `m ≥ 1`; therefore the normalized quantity
`(log K_m - L_m^{K_m,*}) / m` is exactly the visible-entropy rate `log 2`. -/
theorem paper_fold_infonce_exponential_k_stable_expansion {γ : ℝ} (hγ : 0 < γ) :
    (∀ m : ℕ, 1 ≤ m → 2 ≤ fold_infonce_exponential_k_stable_expansion_schedule γ m) ∧
      ∀ m : ℕ, 1 ≤ m →
        fold_infonce_exponential_k_stable_expansion_normalized_gap γ m = Real.log 2 := by
  refine ⟨?_, ?_⟩
  · intro m hm
    exact fold_infonce_exponential_k_stable_expansion_schedule_ge_two hγ hm
  · intro m hm
    have hK :
        2 ≤ fold_infonce_exponential_k_stable_expansion_schedule γ m :=
      fold_infonce_exponential_k_stable_expansion_schedule_ge_two hγ hm
    have hm_real_ne : (m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)
    unfold fold_infonce_exponential_k_stable_expansion_normalized_gap
    rw [Omega.OperatorAlgebra.foldInfoNCELossInfimum_eq m
      (fold_infonce_exponential_k_stable_expansion_schedule γ m) hK]
    unfold Omega.OperatorAlgebra.foldInfoNCEVisibleEntropy
    field_simp [hm_real_ne]
    ring

end

end Omega.Folding
