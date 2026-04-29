import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-replica-softcore-exceptional-charpoly-linear-coefficient`. The Vieta
linear coefficient reduces to the product certificate times the reciprocal-sum certificate. -/
theorem paper_pom_replica_softcore_exceptional_charpoly_linear_coefficient (q : Nat)
    (fib coeff prod recip : Rat)
    (hprod : prod = (-1 : Rat) ^ (q * (q + 1) / 2) / (2 : Rat) ^ q)
    (hrecip : recip = -1 + 2 * (-1 : Rat) ^ q * fib)
    (hcoeff : coeff = (-1 : Rat) ^ q * prod * recip) :
    coeff =
      (-1 : Rat) ^ (q * (q + 1) / 2) / (2 : Rat) ^ q * (2 * fib - (-1 : Rat) ^ q) := by
  subst coeff
  rw [hprod, hrecip]
  set sign : Rat := (-1 : Rat) ^ q
  set scale : Rat := (-1 : Rat) ^ (q * (q + 1) / 2) / (2 : Rat) ^ q
  have hsign_sq : sign * sign = 1 := by
    dsimp [sign]
    rw [← pow_add]
    rw [show q + q = 2 * q by omega]
    rw [pow_mul]
    norm_num
  calc
    sign * scale * (-1 + 2 * sign * fib) =
        scale * (2 * fib * (sign * sign) - sign) := by ring
    _ = scale * (2 * fib - sign) := by
      rw [hsign_sq]
      ring

end Omega.POM
