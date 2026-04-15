import Omega.Core.WalshStokesSingleton
import Mathlib.Tactic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Omega.Core

open scoped BigOperators symmDiff

/-- Walsh character attached to a coordinate subset.
    def:spg-walsh-fourier-inversion-completeness -/
def walshChar (I : Finset (Fin n)) (w : Word n) : ℤ :=
  ∏ i ∈ I, if w i = true then (-1 : ℤ) else 1

/-- Walsh bias coefficient of an integer-valued observable.
    def:spg-walsh-fourier-inversion-completeness -/
def walshBias (f : Word n → ℤ) (I : Finset (Fin n)) : ℤ :=
  ∑ w : Word n, walshChar I w * f w

@[simp] theorem walshChar_empty (w : Word n) : walshChar ∅ w = 1 := by
  simp [walshChar]

@[simp] theorem walshChar_insert {I : Finset (Fin n)} {i : Fin n} (hi : i ∉ I) (w : Word n) :
    walshChar (insert i I) w = (if w i = true then (-1 : ℤ) else 1) * walshChar I w := by
  simp [walshChar, hi]

theorem walshChar_erase {I : Finset (Fin n)} {i : Fin n} (hi : i ∈ I) (w : Word n) :
    walshChar I w = (if w i = true then (-1 : ℤ) else 1) * walshChar (I.erase i) w := by
  conv_lhs => rw [← Finset.insert_erase hi]
  rw [walshChar_insert (Finset.notMem_erase i I)]

/-- Pointwise square of a Walsh character is trivial.
    lem:spg-walsh-fourier-inversion-completeness -/
theorem walshChar_mul_self (I : Finset (Fin n)) (w : Word n) :
    walshChar I w * walshChar I w = 1 := by
  unfold walshChar
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  by_cases h : w i = true <;> simp [h]

private theorem symmDiff_insert_mem {i : Fin n} {I J : Finset (Fin n)} (hi : i ∉ I) (hij : i ∈ J) :
    insert i I ∆ J = I ∆ J.erase i := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_erase, ne_eq]
  by_cases hx : x = i
  · subst hx; simp [hi, hij]
  · simp [hx]

private theorem symmDiff_insert_not_mem {i : Fin n} {I J : Finset (Fin n)}
    (hi : i ∉ I) (hij : i ∉ J) :
    insert i I ∆ J = insert i (I ∆ J) := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_insert]
  by_cases hx : x = i
  · subst hx; simp [hi, hij]
  · simp [hx]

/-- Product of Walsh characters is the character of the symmetric difference.
    lem:spg-walsh-fourier-inversion-completeness -/
theorem walshChar_mul (I J : Finset (Fin n)) (w : Word n) :
    walshChar I w * walshChar J w = walshChar (I ∆ J) w := by
  classical
  induction I using Finset.induction_on generalizing J with
  | empty =>
      have : (∅ : Finset (Fin n)) ∆ J = J := by simp [symmDiff_comm]
      simp [walshChar, this]
  | @insert i I hi ih =>
      by_cases hij : i ∈ J
      · have hsquare :
            (if w i = true then (-1 : ℤ) else 1) * (if w i = true then (-1 : ℤ) else 1) = 1 := by
          by_cases hwi : w i = true <;> simp [hwi]
        have hset := symmDiff_insert_mem hi hij
        calc
          walshChar (insert i I) w * walshChar J w
              = ((if w i = true then (-1 : ℤ) else 1) * walshChar I w) *
                  ((if w i = true then (-1 : ℤ) else 1) * walshChar (J.erase i) w) := by
                    rw [walshChar_insert hi, walshChar_erase hij]
          _ = ((if w i = true then (-1 : ℤ) else 1) * (if w i = true then (-1 : ℤ) else 1)) *
                (walshChar I w * walshChar (J.erase i) w) := by ring
          _ = 1 * (walshChar I w * walshChar (J.erase i) w) := by rw [hsquare]
          _ = walshChar I w * walshChar (J.erase i) w := by ring
          _ = walshChar (I ∆ J.erase i) w := ih (J.erase i)
          _ = walshChar (insert i I ∆ J) w := by rw [hset]
      · have hnot : i ∉ I ∆ J := by
          simp [Finset.mem_symmDiff, hi, hij]
        have hset := symmDiff_insert_not_mem hi hij
        calc
          walshChar (insert i I) w * walshChar J w
              = (if w i = true then (-1 : ℤ) else 1) * (walshChar I w * walshChar J w) := by
                rw [walshChar_insert hi]; ring
          _ = (if w i = true then (-1 : ℤ) else 1) * walshChar (I ∆ J) w := by rw [ih J]
          _ = walshChar (insert i (I ∆ J)) w := by rw [walshChar_insert hnot]
          _ = walshChar (insert i I ∆ J) w := by rw [hset]

theorem walshChar_flipBit_of_mem {I : Finset (Fin n)} {i : Fin n} (hi : i ∈ I) (w : Word n) :
    walshChar I (flipBit i w) = -walshChar I w := by
  have hrest : walshChar (I.erase i) (flipBit i w) = walshChar (I.erase i) w := by
    unfold walshChar
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [flipBit_apply_ne, hji]
  rw [walshChar_erase hi, walshChar_erase hi, hrest]
  by_cases hwi : w i = true
  · simp [flipBit_apply_same, hwi]
  · have hfalse : w i = false := by cases h : w i <;> simp_all
    simp [flipBit_apply_same, hfalse]

/-- Orthogonality of distinct Walsh characters over the finite cube.
    lem:spg-walsh-fourier-inversion-completeness -/
theorem walshChar_orthogonal_sum (I J : Finset (Fin n)) :
    ∑ w : Word n, walshChar I w * walshChar J w =
      if I = J then (2 : ℤ) ^ n else 0 := by
  classical
  by_cases hIJ : I = J
  · subst hIJ
    simp only [if_true]
    calc
      ∑ w : Word n, walshChar I w * walshChar I w = ∑ _w : Word n, (1 : ℤ) := by
        refine Finset.sum_congr rfl ?_
        intro w _
        exact walshChar_mul_self I w
      _ = (Fintype.card (Word n) : ℤ) := by simp
      _ = (2 : ℤ) ^ n := by simp [Word]
  · let s : Finset (Fin n) := I ∆ J
    have hsne : s.Nonempty := Finset.symmDiff_nonempty.mpr hIJ
    obtain ⟨i, hi⟩ := hsne
    have hsum : ∑ w : Word n, walshChar s w = ∑ w : Word n, walshChar s (flipBit i w) := by
      let e : Word n ≃ Word n :=
        { toFun := flipBit i
          invFun := flipBit i
          left_inv := flipBit_involutive i
          right_inv := flipBit_involutive i }
      exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    have hneg : ∑ w : Word n, walshChar s w = -∑ w : Word n, walshChar s w := by
      conv_lhs => rw [hsum]
      simp_rw [walshChar_flipBit_of_mem hi]
      rw [Finset.sum_neg_distrib]
    have hzero : ∑ w : Word n, walshChar s w = 0 := by linarith
    have hmulsum : ∑ w : Word n, walshChar I w * walshChar J w =
        ∑ w : Word n, walshChar s w := by
      refine Finset.sum_congr rfl ?_
      intro w _
      exact walshChar_mul I J w
    rw [hmulsum, hzero]
    simp [hIJ]

/-- Bias coefficients of a Walsh basis vector are diagonal.
    lem:spg-walsh-fourier-inversion-completeness -/
theorem walshBias_expand_basis (I J : Finset (Fin n)) :
    walshBias (fun w => walshChar J w) I = if I = J then (2 : ℤ) ^ n else 0 := by
  simpa [walshBias, mul_comm] using walshChar_orthogonal_sum I J

theorem walshChar_mul_words (I : Finset (Fin n)) (u w : Word n) :
    walshChar I u * walshChar I w =
      ∏ i ∈ I, (if u i = w i then 1 else (-1 : ℤ)) := by
  unfold walshChar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro i _
  by_cases hu : u i = true <;> by_cases hw : w i = true <;> simp [hu, hw]

/-- Walsh kernel reproduces the Kronecker delta on the finite cube.
    lem:spg-walsh-fourier-inversion-completeness -/
theorem walshKernel_delta (u w : Word n) :
    ∑ I : Finset (Fin n), walshChar I u * walshChar I w =
      if u = w then (2 : ℤ) ^ n else 0 := by
  classical
  calc
    ∑ I : Finset (Fin n), walshChar I u * walshChar I w
        = ∑ I ∈ (Finset.univ : Finset (Fin n)).powerset,
            ∏ i ∈ I, (if u i = w i then 1 else (-1 : ℤ)) := by
              simp [walshChar_mul_words]
    _ = ∏ i ∈ (Finset.univ : Finset (Fin n)), (1 + if u i = w i then 1 else (-1 : ℤ)) := by
          symm
          exact Finset.prod_one_add (s := (Finset.univ : Finset (Fin n)))
            (f := fun i => if u i = w i then (1 : ℤ) else -1)
    _ = if u = w then (2 : ℤ) ^ n else 0 := by
          by_cases huw : u = w
          · subst huw
            simp [Finset.prod_const]
          · have hex : ∃ i : Fin n, u i ≠ w i := by
              by_contra h; push_neg at h; exact huw (funext h)
            rcases hex with ⟨i, hi⟩
            rw [show (Finset.univ : Finset (Fin n)) = insert i (Finset.univ.erase i) by
              symm; exact Finset.insert_erase (Finset.mem_univ i)]
            rw [Finset.prod_insert (Finset.notMem_erase i _)]
            simp [hi, huw]

/-- Fourier--Walsh inversion on the finite cube; the bias family determines the observable.
    cor:spg-walsh-fourier-inversion-completeness -/
theorem paper_walsh_fourier_inversion_completeness (f : Word n → ℤ) (w : Word n) :
    ((2 : ℤ) ^ n) * f w = ∑ I : Finset (Fin n), walshBias f I * walshChar I w := by
  classical
  symm
  calc
    ∑ I : Finset (Fin n), walshBias f I * walshChar I w
        = ∑ I : Finset (Fin n), ∑ u : Word n, (walshChar I u * walshChar I w) * f u := by
            refine Finset.sum_congr rfl ?_
            intro I _
            simp only [walshBias, Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro u _
            ring
    _ = ∑ u : Word n, ∑ I : Finset (Fin n), (walshChar I u * walshChar I w) * f u := by
          rw [Finset.sum_comm]
    _ = ∑ u : Word n, (∑ I : Finset (Fin n), walshChar I u * walshChar I w) * f u := by
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [← Finset.sum_mul]
    _ = ∑ u : Word n, (if u = w then (2 : ℤ) ^ n else 0) * f u := by
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [walshKernel_delta]
    _ = ((2 : ℤ) ^ n) * f w := by simp

end Omega.Core
