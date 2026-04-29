import Mathlib.Tactic
import Omega.POM.PrimeRegisterGodelFactorialPointwise

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-time-part9k-coprime-ledger-memory-horizon`.
If each coprime ledger address has size at least `t + 2`, then its product dominates
`(T + 1)!`; composing with the bit-ledger upper bound gives the claimed horizon. -/
theorem paper_xi_time_part9k_coprime_ledger_memory_horizon (M T B : Nat) (p : Fin T -> Nat)
    (hp : forall t, t.1 + 2 <= p t) (hledger : (Finset.univ.prod p) ^ M <= 2 ^ B) :
    (Nat.factorial (T + 1)) ^ M <= 2 ^ B := by
  have hfactorial_le_prod :
      Nat.factorial (T + 1) <= Finset.univ.prod (fun t : Fin T => p t) :=
    Omega.POM.paper_pom_prime_register_godel_factorial_pointwise T p hp
  exact le_trans (Nat.pow_le_pow_left hfactorial_le_prod M) hledger

end Omega.Zeta
