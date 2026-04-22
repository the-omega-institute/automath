import Mathlib.Data.Nat.Prime.Basic
import Omega.EA.FoldGroupoidAutPi1AllPrimes

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-pi1-all-primes`. The conclusion-level `π₁` prime-torsion
statement is the direct re-export of the established fold-groupoid automorphism result from the
emergent-arithmetic chapter. -/
theorem paper_conclusion_pi1_all_primes (p : ℕ) :
    Nat.Prime p → ∃ m : ℕ, p ∣ Omega.EA.foldGroupoidAutPi1OrderProxy m := by
  intro hp
  exact (Omega.EA.paper_fold_groupoid_aut_pi1_all_primes).2 p hp

end Omega.Conclusion
