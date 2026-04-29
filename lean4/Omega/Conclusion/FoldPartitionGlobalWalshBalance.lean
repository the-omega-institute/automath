import Mathlib.Tactic
import Omega.Conclusion.FoldWalshGramSimplexSignatureSection

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

local instance conclusion_fold_partition_global_walsh_balance_decidableEqWord
    (m : ℕ) : DecidableEq (Word m) :=
  Classical.decEq _

local instance conclusion_fold_partition_global_walsh_balance_decidableEqX
    (m : ℕ) : DecidableEq (X m) :=
  Classical.decEq _

/-- The theorem's `H_x` generating-function specialization at a Walsh sign vector. -/
def conclusion_fold_partition_global_walsh_balance_H
    (m : ℕ) (x : X m) (I : Finset (Fin m)) : ℝ :=
  walshProfile m x I

/-- The fiber Walsh coefficient `W_x(I)`. -/
def conclusion_fold_partition_global_walsh_balance_W
    (m : ℕ) (x : X m) (I : Finset (Fin m)) : ℝ :=
  walshProfile m x I

/-- Paper-facing predicate for `thm:conclusion-fold-partition-global-walsh-balance`. -/
def conclusion_fold_partition_global_walsh_balance_statement (m : ℕ) : Prop :=
  ∀ I : Finset (Fin m), I.Nonempty →
    (∑ x : X m, conclusion_fold_partition_global_walsh_balance_W m x I = 0) ∧
      (∑ x : X m, conclusion_fold_partition_global_walsh_balance_H m x I = 0) ∧
      (∑ x : X m, conclusion_fold_partition_global_walsh_balance_H m x I =
        ∑ x : X m, conclusion_fold_partition_global_walsh_balance_W m x I)

def conclusion_fold_partition_global_walsh_balance_flip
    {m : ℕ} (i : Fin m) (w : Word m) : Word m :=
  Function.update w i (!(w i))

@[simp] lemma conclusion_fold_partition_global_walsh_balance_flip_same
    {m : ℕ} (i : Fin m) (w : Word m) :
    conclusion_fold_partition_global_walsh_balance_flip i w i = !(w i) := by
  simp [conclusion_fold_partition_global_walsh_balance_flip]

@[simp] lemma conclusion_fold_partition_global_walsh_balance_flip_ne
    {m : ℕ} (i : Fin m) (w : Word m) {j : Fin m} (h : j ≠ i) :
    conclusion_fold_partition_global_walsh_balance_flip i w j = w j := by
  simp [conclusion_fold_partition_global_walsh_balance_flip, Function.update, h]

@[simp] lemma conclusion_fold_partition_global_walsh_balance_flip_involutive
    {m : ℕ} (i : Fin m) (w : Word m) :
    conclusion_fold_partition_global_walsh_balance_flip i
      (conclusion_fold_partition_global_walsh_balance_flip i w) = w := by
  funext j
  by_cases h : j = i
  · subst h
    simp [conclusion_fold_partition_global_walsh_balance_flip]
  · simp [conclusion_fold_partition_global_walsh_balance_flip, Function.update, h]

lemma conclusion_fold_partition_global_walsh_balance_character_flip_of_mem
    {m : ℕ} {I : Finset (Fin m)} {i : Fin m} (hi : i ∈ I) (w : Word m) :
    walshCharacter m (conclusion_fold_partition_global_walsh_balance_flip i w) I =
      -walshCharacter m w I := by
  have hrest :
      walshCharacter m (conclusion_fold_partition_global_walsh_balance_flip i w) (I.erase i) =
        walshCharacter m w (I.erase i) := by
    unfold walshCharacter
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [coordSign, conclusion_fold_partition_global_walsh_balance_flip_ne, hji]
  have hsign :
      coordSign (conclusion_fold_partition_global_walsh_balance_flip i w) i =
        -coordSign w i := by
    by_cases hwi : w i <;> simp [coordSign, hwi]
  calc
    walshCharacter m (conclusion_fold_partition_global_walsh_balance_flip i w) I
        = walshCharacter m (conclusion_fold_partition_global_walsh_balance_flip i w)
            (insert i (I.erase i)) := by rw [Finset.insert_erase hi]
    _ = coordSign (conclusion_fold_partition_global_walsh_balance_flip i w) i *
          walshCharacter m (conclusion_fold_partition_global_walsh_balance_flip i w)
            (I.erase i) := by
            simp [walshCharacter]
    _ = -(coordSign w i * walshCharacter m w (I.erase i)) := by
            rw [hsign, hrest]
            ring
    _ = -walshCharacter m w (insert i (I.erase i)) := by
            simp [walshCharacter]
    _ = -walshCharacter m w I := by rw [Finset.insert_erase hi]

lemma conclusion_fold_partition_global_walsh_balance_word_sum_zero
    {m : ℕ} {I : Finset (Fin m)} (hI : I.Nonempty) :
    ∑ w : Word m, walshCharacter m w I = 0 := by
  classical
  obtain ⟨i, hi⟩ := hI
  let e : Word m ≃ Word m :=
    { toFun := conclusion_fold_partition_global_walsh_balance_flip i
      invFun := conclusion_fold_partition_global_walsh_balance_flip i
      left_inv := conclusion_fold_partition_global_walsh_balance_flip_involutive i
      right_inv := conclusion_fold_partition_global_walsh_balance_flip_involutive i }
  have hperm :
      ∑ w : Word m, walshCharacter m w I =
        ∑ w : Word m, walshCharacter m (conclusion_fold_partition_global_walsh_balance_flip i w) I := by
    exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
  have hneg :
      ∑ w : Word m, walshCharacter m (conclusion_fold_partition_global_walsh_balance_flip i w) I =
        -∑ w : Word m, walshCharacter m w I := by
    simp_rw [conclusion_fold_partition_global_walsh_balance_character_flip_of_mem hi]
    rw [Finset.sum_neg_distrib]
  linarith

lemma conclusion_fold_partition_global_walsh_balance_sum_profile_zero
    (m : ℕ) {I : Finset (Fin m)} (hI : I.Nonempty) :
    ∑ x : X m, walshProfile m x I = 0 := by
  classical
  have hfiber :
      ∑ x : X m, walshProfile m x I = ∑ w : Word m, walshCharacter m w I := by
    simpa [walshProfile, X.fiber] using
      (Finset.sum_fiberwise_eq_sum_filter
        (s := (Finset.univ : Finset (Word m)))
        (t := (Finset.univ : Finset (X m)))
        (g := Fold)
        (f := fun w : Word m => walshCharacter m w I))
  rw [hfiber]
  exact conclusion_fold_partition_global_walsh_balance_word_sum_zero hI

/-- Paper label: `thm:conclusion-fold-partition-global-walsh-balance`. -/
theorem paper_conclusion_fold_partition_global_walsh_balance (m : ℕ) (hm : 1 ≤ m) :
    conclusion_fold_partition_global_walsh_balance_statement m := by
  intro I hI
  have _ := hm
  have hsum := conclusion_fold_partition_global_walsh_balance_sum_profile_zero m hI
  refine ⟨?_, ?_, ?_⟩
  · simpa [conclusion_fold_partition_global_walsh_balance_W] using hsum
  · simpa [conclusion_fold_partition_global_walsh_balance_H] using hsum
  · rfl

end

end Omega.Conclusion
