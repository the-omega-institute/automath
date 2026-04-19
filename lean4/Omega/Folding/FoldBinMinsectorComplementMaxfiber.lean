import Mathlib.Tactic
import Omega.Folding.MaxFiberHigh

namespace Omega

/-- Paper-facing audited identity: the complement of the minimum-degeneracy sector has the same
cardinality as the maximal Fold fiber at level `2m - 2`. -/
theorem paper_fold_bin_minsector_complement_maxfiber_audited
    (m sectorCard complementCard : Nat)
    (hm : m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12)
    (hsector : sectorCard = Nat.fib m)
    (hcomplement : complementCard = Nat.fib (m + 2) - sectorCard)
    (hmax : Omega.X.maxFiberMultiplicity (2 * m - 2) = Nat.fib (m + 1)) :
    complementCard = Omega.X.maxFiberMultiplicity (2 * m - 2) := by
  have _hm := hm
  subst sectorCard
  subst complementCard
  rw [hmax, Nat.fib_add_two]
  omega

end Omega
