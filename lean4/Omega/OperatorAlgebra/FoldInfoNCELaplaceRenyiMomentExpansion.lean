import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldInfoNCEFiniteKMomentFormula

namespace Omega.OperatorAlgebra

open scoped BigOperators
noncomputable section

lemma neg_one_pow_sub_eq_mul_neg_one_pow (j k : ℕ) (hk : k ≤ j) :
    (-1 : ℝ) ^ (j - k) = (-1 : ℝ) ^ j * (-1 : ℝ) ^ k := by
  have hpow : (-1 : ℝ) ^ j = (-1 : ℝ) ^ (j - k) * (-1 : ℝ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have hk_sq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    calc
      ((-1 : ℝ) ^ k) ^ 2 = (-1 : ℝ) ^ (k + k) := by rw [pow_two, ← pow_add]
      _ = (-1 : ℝ) ^ (2 * k) := by rw [two_mul]
      _ = 1 := by norm_num
  calc
    (-1 : ℝ) ^ (j - k) = (-1 : ℝ) ^ (j - k) * (((-1 : ℝ) ^ k) ^ 2) := by
      rw [hk_sq, mul_one]
    _ = ((-1 : ℝ) ^ (j - k) * (-1 : ℝ) ^ k) * (-1 : ℝ) ^ k := by ring
    _ = (-1 : ℝ) ^ j * (-1 : ℝ) ^ k := by rw [hpow]

lemma foldInfoNCEBeta_succ (K j : ℕ) :
    foldInfoNCEBeta K (j + 1) =
      (Nat.choose (K - 1) j : ℝ) *
        ((-1 : ℝ) ^ j *
          Finset.sum (Finset.range (j + 1))
            (fun k => (Nat.choose j k : ℝ) * (-1 : ℝ) ^ k * Real.log (k + 1))) := by
  unfold foldInfoNCEBeta
  rw [show j + 1 - 1 = j by omega]
  calc
    (↑((K - 1).choose j)) *
        ∑ k ∈ Finset.range (j + 1), ↑(j.choose k) * (-1) ^ (j - k) * Real.log (↑k + 1) =
      (↑((K - 1).choose j)) *
        ∑ k ∈ Finset.range (j + 1), (-1 : ℝ) ^ j * (↑(j.choose k) * (-1) ^ k * Real.log (↑k + 1)) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk' : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [neg_one_pow_sub_eq_mul_neg_one_pow j k hk']
      ring
    _ = (↑((K - 1).choose j)) *
          ((-1 : ℝ) ^ j *
            ∑ k ∈ Finset.range (j + 1), ↑(j.choose k) * (-1) ^ k * Real.log (↑k + 1)) := by
      rw [← Finset.mul_sum]

/-- Paper label: `thm:fold-infonce-laplace-renyi-moment-expansion`. -/
theorem paper_fold_infonce_laplace_renyi_moment_expansion (m K : Nat) :
    let alpha : Nat → Real := fun j =>
      -Finset.sum (Finset.range (j + 1))
        (fun k => ((-1 : Real) ^ k) * (Nat.choose j k : Real) * Real.log (k + 1))
    foldInfoNCEFiniteKMomentExpansion m K =
      Finset.sum (Finset.Icc 1 (K - 1)) (fun j =>
        (((-1 : Real) ^ (j - 1)) * (Nat.choose (K - 1) j : Real) * alpha j) *
          foldCollisionMomentNormalized (j + 1) m) := by
  dsimp
  rw [foldInfoNCEFiniteKMomentExpansion]
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
  change foldInfoNCEBeta K (t + 2) * foldCollisionMomentNormalized (t + 2) m =
    (((-1 : Real) ^ ((t + 1) - 1)) * (Nat.choose (K - 1) (t + 1) : Real) *
        -∑ k ∈ Finset.range (t + 2), (-1 : Real) ^ k * (Nat.choose (t + 1) k : Real) *
          Real.log (k + 1)) *
      foldCollisionMomentNormalized (t + 2) m
  rw [show t + 2 = (t + 1) + 1 by omega, foldInfoNCEBeta_succ]
  set s : ℝ :=
    Finset.sum (Finset.range (t + 2))
      (fun k => (Nat.choose (t + 1) k : ℝ) * (-1 : ℝ) ^ k * Real.log (k + 1))
  have hsub : (t + 1 : ℕ) - 1 = t := by omega
  have hs :
      -∑ k ∈ Finset.range (t + 2), (-1 : Real) ^ k * (Nat.choose (t + 1) k : Real) *
          Real.log (k + 1) = -s := by
    simp [s, mul_assoc, mul_comm]
  rw [pow_succ, hsub, hs]
  ring

end
end Omega.OperatorAlgebra
