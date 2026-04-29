import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Polynomial

/-- Specializing the Witt necklace divisibility identity to `n = p^k` yields the usual Dwork
congruence: every coefficient of `a_{p^k}(u) - a_{p^{k-1}}(u^p)` is divisible by `p^k`.
    cor:witt-dwork-congruence -/
theorem paper_witt_dwork_congruence (p k : Nat) (_hp : Nat.Prime p) (a : Nat → Polynomial Int)
    (q : Polynomial Int)
    (hq :
      ((p ^ k : Int)) • q =
        a (p ^ k) - Polynomial.expand Int p (a (p ^ (k - 1)))) :
    ∀ j,
      ((p ^ k : Int) ∣ (a (p ^ k) - Polynomial.expand Int p (a (p ^ (k - 1)))).coeff j) := by
  intro j
  have hcoeff := congrArg (fun f : Polynomial Int => f.coeff j) hq
  refine ⟨q.coeff j, ?_⟩
  calc
    (a (p ^ k) - Polynomial.expand Int p (a (p ^ (k - 1)))).coeff j
        = (Polynomial.C (p ^ k : Int) * q).coeff j := by
            simpa using hcoeff.symm
    _ = (p ^ k : Int) * q.coeff j := by
          simpa using (Polynomial.coeff_C_mul (p := q) (n := j) (a := (p ^ k : Int)))

end Omega.SyncKernelWeighted
