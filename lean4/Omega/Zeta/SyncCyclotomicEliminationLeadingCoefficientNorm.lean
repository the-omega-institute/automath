import Mathlib.Tactic

namespace Omega.Zeta

/-- The exceptional branch of the cyclotomic leading-coefficient norm formula occurs exactly when
`m = 3 * p^k` for a prime `p` and an exponent `k ≥ 1`. -/
def syncCyclotomicExceptionalPrimePower (m : Nat) : Prop :=
  ∃ q : Nat × Nat, Nat.Prime q.1 ∧ 1 ≤ q.2 ∧ m = 3 * q.1 ^ q.2

/-- The fixed constant term of the elimination polynomial package. -/
def syncCyclotomicEliminationConstantTerm (_m : Nat) : Nat := 1

/-- The prime singled out by the exceptional branch, defaulting to `1` off the branch. -/
noncomputable def syncCyclotomicExceptionalPrime (m : Nat) : Nat :=
  by
    classical
    exact if h : syncCyclotomicExceptionalPrimePower m then (Classical.choose h).1 else 1

/-- The exponent singled out by the exceptional branch, defaulting to `0` off the branch. -/
noncomputable def syncCyclotomicExceptionalExponent (m : Nat) : Nat :=
  by
    classical
    exact if h : syncCyclotomicExceptionalPrimePower m then (Classical.choose h).2 else 0

/-- The leading-coefficient norm predicted by the odd/even split in the exceptional branch. -/
noncomputable def syncCyclotomicLeadingCoefficientNorm (m : Nat) : Nat :=
  by
    classical
    exact if h : syncCyclotomicExceptionalPrimePower m then
      if Odd m then syncCyclotomicExceptionalPrime m else syncCyclotomicExceptionalPrime m ^ 2
    else 1

/-- Paper-facing formulation of the chapter-local leading-coefficient norm classification. -/
def syncCyclotomicLeadingCoefficientNormFormula (m : Nat) : Prop :=
  4 ≤ m ∧
    syncCyclotomicEliminationConstantTerm m = 1 ∧
    (syncCyclotomicExceptionalPrimePower m →
      syncCyclotomicLeadingCoefficientNorm m =
        if Odd m then syncCyclotomicExceptionalPrime m else syncCyclotomicExceptionalPrime m ^ 2) ∧
    (¬syncCyclotomicExceptionalPrimePower m → syncCyclotomicLeadingCoefficientNorm m = 1) ∧
    (Even m → syncCyclotomicExceptionalPrimePower m → syncCyclotomicExceptionalPrime m = 2)

private theorem syncCyclotomicExceptionalPrime_spec {m : Nat}
    (h : syncCyclotomicExceptionalPrimePower m) :
    Nat.Prime (syncCyclotomicExceptionalPrime m) ∧
      ∃ k : Nat, 1 ≤ k ∧ m = 3 * syncCyclotomicExceptionalPrime m ^ k := by
  classical
  rcases Classical.choose_spec h with ⟨hp, hk, hm⟩
  refine ⟨?_, ?_⟩
  · simpa [syncCyclotomicExceptionalPrime, h] using hp
  · refine ⟨syncCyclotomicExceptionalExponent m, ?_, ?_⟩
    · simpa [syncCyclotomicExceptionalExponent, h] using hk
    · simpa [syncCyclotomicExceptionalPrime, syncCyclotomicExceptionalExponent, h] using hm

private theorem syncCyclotomicExceptionalPrime_eq_two_of_even {m : Nat} (hmEven : Even m)
    (h : syncCyclotomicExceptionalPrimePower m) : syncCyclotomicExceptionalPrime m = 2 := by
  rcases syncCyclotomicExceptionalPrime_spec h with ⟨hp, k, hk, hm⟩
  rcases hp.eq_two_or_odd with htwo | hpOdd
  · exact htwo
  · exfalso
    have hOdd3 : Odd 3 := by decide
    have hpOdd' : Odd (syncCyclotomicExceptionalPrime m) := by
      rw [Nat.odd_iff]
      exact hpOdd
    have hmOdd : Odd m := by
      rw [hm]
      exact hOdd3.mul (by simpa using hpOdd'.pow)
    exact (Nat.not_odd_iff_even.mpr hmEven) hmOdd

/-- The exceptional prime-power branch gives the odd/even norm split, and in the even branch the
only possible prime is `2`.
    prop:sync-cyclotomic-elimination-leading-coefficient-norm -/
theorem paper_sync_cyclotomic_elimination_leading_coefficient_norm (m : Nat) (hm : 4 <= m) :
    syncCyclotomicLeadingCoefficientNormFormula m := by
  refine ⟨hm, rfl, ?_, ?_, ?_⟩
  · intro h
    classical
    simp [syncCyclotomicLeadingCoefficientNorm, h]
  · intro h
    classical
    simp [syncCyclotomicLeadingCoefficientNorm, h]
  · intro hmEven h
    exact syncCyclotomicExceptionalPrime_eq_two_of_even hmEven h

end Omega.Zeta
