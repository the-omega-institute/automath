import Mathlib

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- Finite capacity curve attached to a multiset of fiber multiplicities. -/
def foldCapacityCurve (degrees : Finset ℕ) (t : ℕ) : ℕ :=
  Finset.sum degrees (fun d => min d t)

/-- Tail counts `#{d ∈ degrees : t ≤ d}`. -/
def foldTailCount (degrees : Finset ℕ) (t : ℕ) : ℕ :=
  Finset.sum degrees (fun d => if t ≤ d then 1 else 0)

/-- Exact multiplicity counts `#{d ∈ degrees : d = t}`. -/
def foldMultiplicityCount (degrees : Finset ℕ) (t : ℕ) : ℕ :=
  Finset.sum degrees (fun d => if d = t then 1 else 0)

lemma min_sub_min_pred_indicator (d t : ℕ) (ht : 1 ≤ t) :
    (if t ≤ d then 1 else 0) + min d (t - 1) = min d t := by
  by_cases htd : t ≤ d
  · rw [if_pos htd, Nat.min_eq_right htd]
    have hpred : t - 1 ≤ d := by omega
    rw [Nat.min_eq_right hpred]
    omega
  · have hdlt : d < t := lt_of_not_ge htd
    have hdle : d ≤ t - 1 := by omega
    rw [if_neg htd, Nat.min_eq_left (Nat.le_of_lt hdlt), Nat.min_eq_left hdle]
    simp

lemma multiplicity_add_tail_succ (d t : ℕ) :
    (if d = t then 1 else 0) + (if t + 1 ≤ d then 1 else 0) = if t ≤ d then 1 else 0 := by
  by_cases hdt : d = t
  · subst hdt
    simp
  · by_cases htd : t ≤ d
    · have hsucc : t + 1 ≤ d := by omega
      simp [hdt, htd, hsucc]
    · have hsucc : ¬ t + 1 ≤ d := by omega
      simp [hdt, htd, hsucc]

lemma foldTailCount_eq_capacityCurve_sub (degrees : Finset ℕ) (t : ℕ) (ht : 1 ≤ t) :
    foldTailCount degrees t = foldCapacityCurve degrees t - foldCapacityCurve degrees (t - 1) := by
  have hsum :
      foldTailCount degrees t + foldCapacityCurve degrees (t - 1) = foldCapacityCurve degrees t := by
    unfold foldTailCount foldCapacityCurve
    calc
      Finset.sum degrees (fun d => if t ≤ d then 1 else 0) +
          Finset.sum degrees (fun d => min d (t - 1))
          = Finset.sum degrees (fun d => (if t ≤ d then 1 else 0) + min d (t - 1)) := by
              rw [← Finset.sum_add_distrib]
      _ = Finset.sum degrees (fun d => min d t) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            exact min_sub_min_pred_indicator d t ht
  exact Nat.eq_sub_of_add_eq' (by simpa [add_comm] using hsum)

lemma foldMultiplicityCount_eq_tail_sub (degrees : Finset ℕ) (t : ℕ) :
    foldMultiplicityCount degrees t = foldTailCount degrees t - foldTailCount degrees (t + 1) := by
  have hsum :
      foldMultiplicityCount degrees t + foldTailCount degrees (t + 1) = foldTailCount degrees t := by
    unfold foldMultiplicityCount foldTailCount
    calc
      Finset.sum degrees (fun d => if d = t then 1 else 0) +
          Finset.sum degrees (fun d => if t + 1 ≤ d then 1 else 0)
          = Finset.sum degrees (fun d => (if d = t then 1 else 0) + (if t + 1 ≤ d then 1 else 0)) := by
              rw [← Finset.sum_add_distrib]
      _ = Finset.sum degrees (fun d => if t ≤ d then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            exact multiplicity_add_tail_succ d t
  exact Nat.eq_sub_of_add_eq' (by simpa [add_comm] using hsum)

/-- Paper label: `cor:op-algebra-capacity-curve-complete-invariant`. The first forward difference
recovers the tail counts, and the second forward difference recovers the exact multiplicities. -/
theorem paper_op_algebra_capacity_curve_complete_invariant (degrees : Finset ℕ) :
    (∀ t : ℕ, 1 ≤ t →
      foldTailCount degrees t = foldCapacityCurve degrees t - foldCapacityCurve degrees (t - 1)) ∧
      (∀ t : ℕ, 1 ≤ t →
        foldMultiplicityCount degrees t = foldTailCount degrees t - foldTailCount degrees (t + 1)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact foldTailCount_eq_capacityCurve_sub degrees t ht
  · intro t ht
    exact foldMultiplicityCount_eq_tail_sub degrees t

end Omega.OperatorAlgebra
