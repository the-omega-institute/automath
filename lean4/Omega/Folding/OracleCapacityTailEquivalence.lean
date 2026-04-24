import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Folding

open scoped BigOperators

/-- Audited finite histogram used for the capacity/tail layer-cake identity. -/
def auditedFoldHistogram (m : ℕ) (i : Fin (m + 1)) : ℕ :=
  m + 1 - i.1

/-- Continuous-capacity proxy obtained by truncating the histogram at level `T`. -/
def foldContinuousCapacityCurve (m T : ℕ) : ℕ :=
  Finset.univ.sum fun i : Fin (m + 1) => Nat.min (auditedFoldHistogram m i) T

/-- Tail count of the audited histogram above level `t`. -/
def foldTailCount (m t : ℕ) : ℕ :=
  Finset.univ.sum fun i : Fin (m + 1) => if t < auditedFoldHistogram m i then 1 else 0

/-- The truncated capacity curve is the cumulative tail count. -/
def FoldCapacityTailEquivalenceStatement (m : ℕ) : Prop :=
  ∀ T : ℕ, foldContinuousCapacityCurve m T = (Finset.range T).sum fun t => foldTailCount m t

private theorem min_eq_sum_indicator (h T : ℕ) :
    Nat.min h T = (Finset.range T).sum fun t => if t < h then 1 else 0 := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      rw [Finset.sum_range_succ, ← ih]
      by_cases hT : T < h
      · have hsucc : h.min (T + 1) = T + 1 := Nat.min_eq_right (Nat.succ_le_of_lt hT)
        have hcur : h.min T = T := Nat.min_eq_right (Nat.le_of_lt hT)
        rw [hsucc, hcur, if_pos hT]
      · have hh : h ≤ T := Nat.le_of_not_gt hT
        have hsucc : h.min (T + 1) = h := Nat.min_eq_left (Nat.le_trans hh (Nat.le_succ T))
        have hcur : h.min T = h := Nat.min_eq_left hh
        rw [hsucc, hcur, if_neg hT]
        simp

/-- Paper label: `prop:fold-capacity-tail-equivalence`. -/
theorem paper_fold_capacity_tail_equivalence (m : Nat) : FoldCapacityTailEquivalenceStatement m := by
  intro T
  unfold foldContinuousCapacityCurve foldTailCount
  calc
    Finset.univ.sum (fun i : Fin (m + 1) => Nat.min (auditedFoldHistogram m i) T) =
        Finset.univ.sum
          (fun i : Fin (m + 1) => (Finset.range T).sum fun t => if t < auditedFoldHistogram m i then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [min_eq_sum_indicator (auditedFoldHistogram m i) T]
    _ = (Finset.range T).sum
          (fun t => Finset.univ.sum fun i : Fin (m + 1) => if t < auditedFoldHistogram m i then 1 else 0) := by
          rw [Finset.sum_comm]
    _ = (Finset.range T).sum fun t => foldTailCount m t := by
          rfl

end Omega.Folding
