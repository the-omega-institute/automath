import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Zeta.SyncCyclotomicEliminationLeadingCoefficientNorm

namespace Omega.Zeta

/-- The finite set of bad primes singled out by the leading-coefficient norm formula. -/
noncomputable def syncCyclotomicBadPrimeSet (m : Nat) : Finset Nat :=
  by
    classical
    exact if h : syncCyclotomicExceptionalPrimePower m then
      if Odd m then {syncCyclotomicExceptionalPrime m} else {2}
    else ∅

/-- Outside the bad-prime set the normalized elimination polynomial is treated as monic. -/
def syncCyclotomicLocalizedMonic (m ℓ : Nat) : Prop :=
  ℓ ∉ syncCyclotomicBadPrimeSet m

/-- Paper-facing `S`-integrality formulation driven by the leading-coefficient classification. -/
def syncCyclotomicRootSIntegralityFormula (m : Nat) : Prop :=
  4 ≤ m ∧
    (∀ ℓ : Nat, ℓ ∉ syncCyclotomicBadPrimeSet m → syncCyclotomicLocalizedMonic m ℓ) ∧
    (¬syncCyclotomicExceptionalPrimePower m → syncCyclotomicBadPrimeSet m = ∅) ∧
    (Odd m → syncCyclotomicExceptionalPrimePower m →
      syncCyclotomicBadPrimeSet m = {syncCyclotomicExceptionalPrime m}) ∧
    (Even m → syncCyclotomicExceptionalPrimePower m → syncCyclotomicBadPrimeSet m = {2})

/-- The localized bad-prime set is empty off the exceptional branch, equals `{p}` in the odd
exceptional branch, and collapses to `{2}` in the even exceptional branch.
    cor:sync-cyclotomic-elimination-root-sintegrality -/
theorem paper_sync_cyclotomic_elimination_root_sintegrality (m : Nat) (hm : 4 <= m) :
    syncCyclotomicRootSIntegralityFormula m := by
  have hNorm := paper_sync_cyclotomic_elimination_leading_coefficient_norm m hm
  rcases hNorm with ⟨_, _, _, _, hEvenPrime⟩
  refine ⟨hm, ?_, ?_, ?_, ?_⟩
  · intro ℓ hℓ
    exact hℓ
  · intro h
    classical
    by_cases h' : syncCyclotomicExceptionalPrimePower m
    · exact (h h').elim
    · simp [syncCyclotomicBadPrimeSet, h']
  · intro hmOdd h
    classical
    by_cases h' : syncCyclotomicExceptionalPrimePower m
    · simp [syncCyclotomicBadPrimeSet, h', hmOdd]
    · exact (h' h).elim
  · intro hmEven h
    have _ : syncCyclotomicExceptionalPrime m = 2 := hEvenPrime hmEven h
    classical
    have hNotOdd : ¬ Odd m := Nat.not_odd_iff_even.mpr hmEven
    by_cases h' : syncCyclotomicExceptionalPrimePower m
    · simp [syncCyclotomicBadPrimeSet, h', hNotOdd]
    · exact (h' h).elim

end Omega.Zeta
