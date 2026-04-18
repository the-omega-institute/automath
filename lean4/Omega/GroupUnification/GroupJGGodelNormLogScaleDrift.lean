import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.GroupUnification.GroupJGEllipsePrimeHomomorphism

namespace Omega.GroupUnification

lemma groupJGPrimeNorm_log_eq_sum (r : PrimeRegisterObject) :
    Real.log (groupJGPrimeNorm r : Real) =
      Finset.sum r.support (fun i => (r i : Real) * Real.log (groupJGPrime i)) := by
  classical
  have hprod :
      Real.log (groupJGPrimeNorm r : Real) =
        Finset.sum r.support (fun i => Real.log ((groupJGPrime i : Real) ^ r i)) := by
    simpa [groupJGPrimeNorm, Finsupp.prod, Nat.cast_pow] using
      (Real.log_prod (s := r.support) (f := fun i => (groupJGPrime i : Real) ^ r i) (by
        intro i hi
        exact pow_ne_zero (r i) (by exact_mod_cast (groupJGPrime_prime i).ne_zero)))
  rw [hprod]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Real.log_pow]

/-- Scaling the logarithm of the prime-register norm by `n / 2` gives the corresponding scaled
support sum of exponent-weighted prime logs.
    prop:group-jg-godel-norm-log-scale-drift -/
theorem paper_group_jg_godel_norm_log_scale_drift (r : PrimeRegisterObject) (n : Nat) :
    ((n : Real) / 2) * Real.log (groupJGPrimeNorm r : Real) =
      ((n : Real) / 2) *
        Finset.sum r.support (fun i => (r i : Real) * Real.log (groupJGPrime i)) := by
  rw [groupJGPrimeNorm_log_eq_sum]

end Omega.GroupUnification
