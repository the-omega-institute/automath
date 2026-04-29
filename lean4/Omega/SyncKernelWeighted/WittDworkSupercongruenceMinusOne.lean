import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Omega.SyncKernelWeighted.WittDworkCongruence

namespace Omega.SyncKernelWeighted

open Polynomial

/-- Paper label: `cor:witt-dwork-supercongruence-minus1`. Specializing the prime-power Dwork
congruence at `u = -1` and using that odd primes fix `-1` under Frobenius gives the usual
`u = -1` supercongruence. -/
theorem paper_witt_dwork_supercongruence_minus1
    (p k : ℕ) (hp : Nat.Prime p) (hpne2 : p ≠ 2)
    (a : Nat → Polynomial Int) (q : Polynomial Int)
    (hq :
      ((p ^ k : Int)) • q =
        a (p ^ k) - Polynomial.expand Int p (a (p ^ (k - 1)))) :
    ((p ^ k : Int) ∣ (a (p ^ k)).eval (-1) - (a (p ^ (k - 1))).eval (-1)) := by
  let _ := paper_witt_dwork_congruence p k hp a q hq
  have hpOdd : Odd p := hp.odd_of_ne_two hpne2
  have hpow : (-1 : Int) ^ p = -1 := hpOdd.neg_one_pow
  have hexpand :
      (Polynomial.expand Int p (a (p ^ (k - 1)))).eval (-1) =
        (a (p ^ (k - 1))).eval (-1) := by
    rw [Polynomial.expand_eval, hpow]
  refine ⟨q.eval (-1), ?_⟩
  have heval := congrArg (fun f : Polynomial Int => f.eval (-1)) hq
  calc
    (a (p ^ k)).eval (-1) - (a (p ^ (k - 1))).eval (-1)
        = (a (p ^ k) - Polynomial.expand Int p (a (p ^ (k - 1)))).eval (-1) := by
            rw [Polynomial.eval_sub, hexpand]
    _ = (((p ^ k : Int) • q).eval (-1)) := by
          simpa using heval.symm
    _ = (p ^ k : Int) * q.eval (-1) := by
          simp [smul_eq_C_mul]

end Omega.SyncKernelWeighted
