import Mathlib.Tactic
import Omega.CircleDimension.Fibonacci2PowerAdicUnitInfinite
import Omega.CircleDimension.FinitePrimeTruncationKernels

namespace Omega.CircleDimension

/-- A finite-prime observation family has an infinite common kernel if primes outside the observed
support occur arbitrarily far out. -/
def elliptic2PowerTowerCommonKernelInfinite (S : Finset ℕ) : Prop :=
  ∀ N, ∃ p : ComplementPrimeSupport S, N < p.1

/-- The finite-prime dictionary records only the truncation to the observed support. -/
def elliptic2PowerTowerFinitePrimeDictionaryInjective (S : Finset ℕ) : Prop :=
  Function.Injective (universalPrimeTruncationMap S)

/-- No finite-prime dictionary can be injective once a nontrivial complement axis remains. -/
def elliptic2PowerTowerNoFinitePrimeDictionaryInjective (S : Finset ℕ) : Prop :=
  ¬ elliptic2PowerTowerFinitePrimeDictionaryInjective S

/-- Any finite-prime observation of the dyadic elliptic tower misses infinitely many prime axes,
so the common kernel is infinite and the finite-prime dictionary cannot be injective.
    cor:cdim-elliptic-2power-tower-finite-prime-observation-indistinguishable -/
theorem paper_cdim_elliptic_2power_tower_finite_prime_observation_indistinguishable
    (S : Finset ℕ) :
    elliptic2PowerTowerCommonKernelInfinite S ∧
      elliptic2PowerTowerNoFinitePrimeDictionaryInjective S := by
  have _ := paper_cdim_fibonacci_2power_adic_unit_infinite
  refine ⟨?_, ?_⟩
  · intro N
    rcases Nat.exists_infinite_primes (max N (S.sup id) + 1) with ⟨p, hpge, hpprime⟩
    have hp_not_mem : p ∉ S := by
      intro hpS
      have hp_le : p ≤ S.sup id := by
        simpa using (Finset.le_sup hpS : id p ≤ S.sup id)
      have hs_succ_le : S.sup id + 1 ≤ p := by
        exact le_trans (Nat.succ_le_succ (Nat.le_max_right N (S.sup id))) hpge
      omega
    refine ⟨⟨p, hpprime, hp_not_mem⟩, ?_⟩
    have hN_succ_le : N + 1 ≤ p := by
      exact le_trans (Nat.succ_le_succ (Nat.le_max_left N (S.sup id))) hpge
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self N) hN_succ_le
  · intro hInjective
    rcases Nat.exists_infinite_primes (S.sup id + 1) with ⟨p, hpge, hpprime⟩
    have hp_not_mem : p ∉ S := by
      intro hpS
      have hp_le : p ≤ S.sup id := by
        simpa using (Finset.le_sup hpS : id p ≤ S.sup id)
      omega
    let zeroPoint : AllPrimeProduct := 0
    let spike : AllPrimeProduct := fun q => if h : q.1 = p then 1 else 0
    have hMap : universalPrimeTruncationMap S spike = universalPrimeTruncationMap S zeroPoint := by
      ext q
      have hqp : q.1 ≠ p := by
        intro hq
        exact hp_not_mem (hq ▸ q.2.1)
      simp [universalPrimeTruncationMap, spike, zeroPoint, hqp]
    have hNe : spike ≠ zeroPoint := by
      intro hEq
      have hCoord := congrFun hEq ⟨p, hpprime⟩
      simp [spike, zeroPoint] at hCoord
    exact hNe (hInjective hMap)

end Omega.CircleDimension
