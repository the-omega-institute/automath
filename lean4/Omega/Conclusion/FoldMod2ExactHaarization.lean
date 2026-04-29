import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.Fiber

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- Splitting the pushforward sum over the two fibers of a parity map and using that the two
fibers have equal cardinality yields the exact Haar average on `Fin 2`.
    thm:conclusion-fold-mod2-exact-haarization -/
theorem paper_conclusion_fold_mod2_exact_haarization (m : ℕ) (π : Word m → Fin 2) (f : Fin 2 → ℝ)
    (heq :
      (Finset.univ.filter fun ω : Word m => π ω = 0).card =
        (Finset.univ.filter fun ω : Word m => π ω = 1).card) :
    ((∑ ω : Word m, f (π ω)) : ℝ) / (2 : ℝ) ^ m = (f 0 + f 1) / 2 := by
  classical
  let S0 : Finset (Word m) := Finset.univ.filter fun ω : Word m => π ω = 0
  let S1 : Finset (Word m) := Finset.univ.filter fun ω : Word m => π ω = 1
  have fin2_ne_zero_eq_one {a : Fin 2} (h : a ≠ 0) : a = 1 := by
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨j, rfl⟩
    · contradiction
    · fin_cases j
      rfl
  have hS1_not :
      (Finset.univ.filter fun ω : Word m => π ω ≠ 0) = S1 := by
    ext ω
    simp [S1]
    constructor
    · intro hneq
      exact fin2_ne_zero_eq_one hneq
    · intro hone
      simp [hone]
  have hsplit :
      ((∑ ω : Word m, f (π ω)) : ℝ) = S0.sum (fun _ => f 0) + S1.sum (fun _ => f 1) := by
    calc
      ((∑ ω : Word m, f (π ω)) : ℝ)
          = (Finset.univ.filter (fun ω : Word m => π ω = 0)).sum (fun ω => f (π ω)) +
              (Finset.univ.filter (fun ω : Word m => π ω ≠ 0)).sum (fun ω => f (π ω)) := by
                symm
                simpa using
                  (Finset.sum_filter_add_sum_filter_not
                    (s := (Finset.univ : Finset (Word m))) (p := fun ω : Word m => π ω = 0)
                    (f := fun ω => f (π ω)))
      _ = S0.sum (fun _ => f 0) + (Finset.univ.filter (fun ω : Word m => π ω ≠ 0)).sum
            (fun ω => f (π ω)) := by
              rw [show (Finset.univ.filter (fun ω : Word m => π ω = 0)) = S0 by rfl]
              congr 1
              exact Finset.sum_congr rfl (by intro ω hω; simp [S0] at hω; simp [hω])
      _ = S0.sum (fun _ => f 0) + S1.sum (fun _ => f 1) := by
              rw [hS1_not]
              congr 1
              exact Finset.sum_congr rfl (by intro ω hω; simp [S1] at hω; simp [hω])
  have hS0 :
      S0.sum (fun _ => f 0) = (S0.card : ℝ) * f 0 := by
    simp [S0]
  have hS1 :
      S1.sum (fun _ => f 1) = (S1.card : ℝ) * f 1 := by
    simp [S1]
  have hcard_eq : (S0.card : ℝ) = S1.card := by
    exact_mod_cast heq
  have hcard_total :
      (S0.card : ℝ) + S1.card = (2 : ℝ) ^ m := by
    have hpart_nat :
        S0.card + S1.card = Fintype.card (Word m) := by
      calc
        S0.card + S1.card
            = (Finset.univ.filter (fun ω : Word m => π ω = 0)).card +
                (Finset.univ.filter (fun ω : Word m => π ω ≠ 0)).card := by
                  rw [show (Finset.univ.filter (fun ω : Word m => π ω = 0)) = S0 by rfl, hS1_not]
        _ = (Finset.univ : Finset (Word m)).card := by
              simpa using
                (Finset.card_filter_add_card_filter_not
                  (s := (Finset.univ : Finset (Word m))) (p := fun ω : Word m => π ω = 0))
        _ = Fintype.card (Word m) := by simp
    have hcard_word : (Fintype.card (Word m) : ℝ) = (2 : ℝ) ^ m := by
      simp [Omega.Word]
    calc
      (S0.card : ℝ) + S1.card = (Fintype.card (Word m) : ℝ) := by
        exact_mod_cast hpart_nat
      _ = (2 : ℝ) ^ m := hcard_word
  have hhalf : (S0.card : ℝ) = (2 : ℝ) ^ m / 2 := by
    nlinarith [hcard_eq, hcard_total]
  have hhalf' : (S1.card : ℝ) = (2 : ℝ) ^ m / 2 := by
    nlinarith [hcard_eq, hhalf]
  have hpow_ne : (2 : ℝ) ^ m ≠ 0 := by positivity
  calc
    ((∑ ω : Word m, f (π ω)) : ℝ) / (2 : ℝ) ^ m
        = (((S0.card : ℝ) * f 0) + ((S1.card : ℝ) * f 1)) / (2 : ℝ) ^ m := by
            rw [hsplit, hS0, hS1]
    _ = (((2 : ℝ) ^ m / 2) * (f 0 + f 1)) / (2 : ℝ) ^ m := by
          rw [hhalf, hhalf']
          ring
    _ = (f 0 + f 1) / 2 := by
          have hfinal :
              (((2 : ℝ) ^ m / 2) * (f 0 + f 1)) / (2 : ℝ) ^ m = (f 0 + f 1) / 2 := by
            field_simp [hpow_ne]
          exact hfinal

end

end Omega.Conclusion
