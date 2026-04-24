import Mathlib.Tactic

open scoped BigOperators

namespace Omega.CircleDimension

variable {ι : Type*} [DecidableEq ι]

/-- The `i`-th mixed-localization `p^k`-quotient cardinality: it is trivial when `p ∈ S i`, and
otherwise contributes one copy of `ZMod (p^k)`, hence cardinality `p^k`. -/
def mixedLocalizationPkSummandCard (S : ι → Finset ℕ) (p k : ℕ) (i : ι) : ℕ :=
  if p ∈ S i then 1 else p ^ k

/-- The recovered prime-ledger multiplicity `m_p`: the number of summands whose localization does
not invert `p`. -/
def mixedLocalizationMp (I : Finset ι) (S : ι → Finset ℕ) (p : ℕ) : ℕ :=
  (I.filter fun i => p ∉ S i).card

lemma mixedLocalizationPkSummandCard_prod
    (I : Finset ι) (S : ι → Finset ℕ) (p k : ℕ) :
    (∏ i ∈ I, mixedLocalizationPkSummandCard S p k i) = (p ^ k) ^ mixedLocalizationMp I S p := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      simp [mixedLocalizationMp]
  | @insert a I ha hI =>
      by_cases hp : p ∈ S a
      · rw [Finset.prod_insert ha, mixedLocalizationPkSummandCard, if_pos hp, one_mul]
        have hmp : mixedLocalizationMp (insert a I) S p = mixedLocalizationMp I S p := by
          unfold mixedLocalizationMp
          rw [Finset.filter_insert, if_neg (by simpa using hp)]
        rw [hI, hmp]
      · rw [Finset.prod_insert ha, mixedLocalizationPkSummandCard, if_neg hp, hI]
        have hmp : mixedLocalizationMp (insert a I) S p = mixedLocalizationMp I S p + 1 := by
          unfold mixedLocalizationMp
          rw [Finset.filter_insert, if_pos hp]
          have hnotmem : a ∉ I.filter fun i => p ∉ S i := by
            simp [ha]
          rw [Finset.card_insert_of_notMem hnotmem]
        rw [hmp]
        simp [pow_succ, Nat.mul_comm]

/-- In the concrete mixed-localization bookkeeping model, each summand contributes either a trivial
`p^k`-quotient or a copy of `ZMod (p^k)`, so multiplying the quotient cardinalities recovers the
prime-ledger exponent `m_p`.
    thm:cdim-star-mixed-localization-pk-growth-inversion -/
theorem paper_cdim_star_mixed_localization_pk_growth_inversion
    (I : Finset ι) (S : ι → Finset ℕ) (p k : ℕ) :
    (∏ i ∈ I, mixedLocalizationPkSummandCard S p k i) =
      p ^ (k * mixedLocalizationMp I S p) := by
  calc
    (∏ i ∈ I, mixedLocalizationPkSummandCard S p k i)
      = (p ^ k) ^ mixedLocalizationMp I S p := mixedLocalizationPkSummandCard_prod I S p k
    _ = p ^ (k * mixedLocalizationMp I S p) := by rw [pow_mul]

end Omega.CircleDimension
