import Omega.EA.PrimeRegisterMultiplicativeNormalizationAdditiveIso
import Omega.EA.PrimeRegisterNormalFormUniqueness
import Omega.Folding.Fiber

namespace Omega.EA

open Omega.Rewrite

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: the finite Zeckendorf quotient is witnessed by the bijectivity of the
    stable-value map and by the Fibonacci cardinality of admissible representatives.
    thm:monoid-quotient-is-N -/
theorem paper_zeckendorf_monoid_quotient_is_N_seeds (m : Nat) :
    Function.Bijective (Omega.X.stableValueFin (m := m)) ∧
      Fintype.card (Omega.X m) = Nat.fib (m + 2) := by
  exact ⟨Omega.X.paper_monoid_quotient_is_N m, Omega.X.card_eq_fib m⟩

set_option maxHeartbeats 400000 in
/-- Paper-facing quotient package: the finite stable-value quotient is enumerated by the Fibonacci
    interval `Fin (fib (m+2))`, every class has a unique stable representative, the normalized
    prime-register product is addition on `ℕ`, and irreducible representatives are uniquely
    determined by their Zeckendorf value.
    thm:monoid-quotient-is-N -/
theorem paper_monoid_quotient_is_n (m : Nat) :
    Function.Bijective (Omega.X.stableValueFin (m := m)) ∧
      Fintype.card (Omega.X m) = Nat.fib (m + 2) ∧
      (∀ n : Fin (Nat.fib (m + 2)), ∃! x : Omega.X m, Omega.X.stableValueFin x = n) ∧
      (∀ a b : DigitCfg, Relation.ReflTransGen Step a b → Irreducible b → b = R_F (valPr a)) ∧
      (∀ n k : ℕ, NF_pr (primeRegisterMul (R_F n) (R_F k)) = R_F (n + k)) := by
  refine ⟨Omega.X.paper_monoid_quotient_is_N m, Omega.X.card_eq_fib m, ?_, ?_, ?_⟩
  · intro n
    rcases (Omega.X.paper_monoid_quotient_is_N m).2 n with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact (Omega.X.paper_monoid_quotient_is_N m).1 (hy.trans hx.symm)
  · intro a b hab hbIrr
    exact (paper_prime_register_normal_form_uniqueness a).2.2 b hab hbIrr
  · intro n k
    exact (paper_prime_register_multiplicative_normalization_additive_iso).2.1 n k

end Omega.EA
