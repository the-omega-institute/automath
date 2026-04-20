import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for a cofinal prime exhaustion: a chosen prime enumeration together with finite
support witnesses capturing each enumerated prime. -/
structure CofinalPrimeExhaustionData where
  primeAt : Nat → Nat
  primeAt_prime : ∀ n, Nat.Prime (primeAt n)
  coversPrime : ∀ p : Nat, Nat.Prime p → ∃ n, primeAt n = p
  supportWitness : Nat → Finset Nat
  prime_mem_supportWitness : ∀ n, primeAt n ∈ supportWitness n

namespace CofinalPrimeExhaustionData

/-- The explicit stage formed from the union of the first `n + 1` support witnesses. -/
def supportUnion (D : CofinalPrimeExhaustionData) (n : Nat) : Finset Nat :=
  (Finset.range (n + 1)).biUnion D.supportWitness

/-- A finite stage is built from supports when it is one of these explicit initial unions. -/
def stageBuiltFromSupports (D : CofinalPrimeExhaustionData) (s : Finset Nat) : Prop :=
  ∃ n, s = D.supportUnion n

end CofinalPrimeExhaustionData

open CofinalPrimeExhaustionData

/-- Build a monotone chain of finite prime supports by taking finite unions of support witnesses;
every prime eventually appears because the chosen enumeration is exhaustive.
    thm:xi-time-part62ae-cofinal-prime-exhaustion -/
theorem paper_xi_time_part62ae_cofinal_prime_exhaustion (D : CofinalPrimeExhaustionData) :
    ∃ chain : Nat -> Finset Nat, (forall n, chain n ⊆ chain (n + 1)) ∧
      (forall n, D.stageBuiltFromSupports (chain n)) ∧
      (forall p : Nat, Nat.Prime p -> ∃ n, p ∈ chain n) := by
  classical
  refine ⟨D.supportUnion, ?_, ?_, ?_⟩
  · intro n x hx
    rcases Finset.mem_biUnion.mp hx with ⟨k, hk, hxk⟩
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hk)
      (Nat.lt_succ_self (n + 1))), hxk⟩
  · intro n
    exact ⟨n, rfl⟩
  · intro p hp
    rcases D.coversPrime p hp with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← hn]
    exact Finset.mem_biUnion.mpr
      ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), D.prime_mem_supportWitness n⟩

end Omega.Zeta
