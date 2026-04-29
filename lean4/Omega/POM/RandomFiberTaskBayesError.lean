import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- Paper label: `thm:pom-random-fiber-task-bayes-error`. -/
theorem paper_pom_random_fiber_task_bayes_error {alpha : Type} [Fintype alpha]
    [DecidableEq alpha] (w : alpha → Real) (k : Nat) :
    (1 / 2 : Real) * Finset.univ.sum (fun x => w x * (1 - w x) ^ k) =
      (1 / 2 : Real) *
        Finset.sum (Finset.range (k + 1))
          (fun j => (-1 : Real) ^ j * (Nat.choose k j : Real) *
            Finset.univ.sum (fun x => (w x) ^ (j + 1))) := by
  have hExpand :
      Finset.univ.sum (fun x => w x * (1 - w x) ^ k) =
        Finset.sum (Finset.range (k + 1))
          (fun j => (-1 : Real) ^ j * (Nat.choose k j : Real) *
            Finset.univ.sum (fun x => (w x) ^ (j + 1))) := by
    calc
      Finset.univ.sum (fun x => w x * (1 - w x) ^ k) =
          Finset.univ.sum (fun x =>
            Finset.sum (Finset.range (k + 1))
              (fun j => (-1 : Real) ^ j * (Nat.choose k j : Real) * (w x) ^ (j + 1))) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hBinomial :
                (1 - w x) ^ k =
                  Finset.sum (Finset.range (k + 1))
                    (fun j => (Nat.choose k j : Real) * (-w x) ^ j * 1 ^ (k - j)) := by
              rw [sub_eq_add_neg, add_comm]
              simpa [mul_assoc, mul_left_comm, mul_comm] using (add_pow (-w x) (1 : Real) k)
            calc
              w x * (1 - w x) ^ k =
                  w x * Finset.sum (Finset.range (k + 1))
                    (fun j => (Nat.choose k j : Real) * (-w x) ^ j * 1 ^ (k - j)) := by
                      rw [hBinomial]
              _ = Finset.sum (Finset.range (k + 1))
                    (fun j => w x * ((Nat.choose k j : Real) * (-w x) ^ j * 1 ^ (k - j))) := by
                      rw [Finset.mul_sum]
              _ = Finset.sum (Finset.range (k + 1))
                    (fun j => (-1 : Real) ^ j * (Nat.choose k j : Real) * (w x) ^ (j + 1)) := by
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      rw [one_pow, show -(w x) = (-1 : Real) * w x by ring, mul_pow, pow_succ]
                      ring
      _ = Finset.sum (Finset.range (k + 1))
            (fun j => Finset.univ.sum
              (fun x => (-1 : Real) ^ j * (Nat.choose k j : Real) * (w x) ^ (j + 1))) := by
            rw [Finset.sum_comm]
      _ = Finset.sum (Finset.range (k + 1))
            (fun j => (-1 : Real) ^ j * (Nat.choose k j : Real) *
              Finset.univ.sum (fun x => (w x) ^ (j + 1))) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [← Finset.mul_sum]
  exact congrArg (fun t => (1 / 2 : Real) * t) hExpand

end Omega.POM
