import Mathlib.Tactic
import Mathlib.Data.Nat.Totient

/-!
# Localized quotient index ledger seeds

For a localized number system G_S = Z[S⁻¹], the finite quotient G_S/nG_S ≅ Z/n_{S⊥}Z
where n_{S⊥} := n / ∏_{p∈S} p^{v_p(n)} strips all S-part from n.

The index [G_S : nG_S] = n_{S⊥}, and Z/mZ appears in the finite quotients of G_S
iff all prime factors of m lie outside S.

## Seed values for S = {2, 3}

n_{S⊥} stripping:
- n = 12 = 2² · 3: n_{S⊥} = 1 (all primes in S)
- n = 30 = 2 · 3 · 5: n_{S⊥} = 5 (strip 2,3 keep 5)
- n = 7: n_{S⊥} = 7 (7 ∉ S, no stripping)
- n = 60 = 2² · 3 · 5: n_{S⊥} = 5
- n = 35 = 5 · 7: n_{S⊥} = 35 (both primes outside S)

Euler totient of stripped values:
- φ(1) = 1, φ(5) = 4, φ(7) = 6, φ(35) = 24

## Paper references

- thm:xi-localized-quotient-index-ledger
-/

namespace Omega.Zeta.QuotientIndexLedgerSeeds

/-! ## S-stripping function

For S = {2, 3}, the S⊥-part of n removes all factors of 2 and 3. -/

/-- Strip all factors of 2 and 3 from n.
    thm:xi-localized-quotient-index-ledger -/
def stripS23 (n : ℕ) : ℕ := n / (2 ^ n.factorization 2 * 3 ^ n.factorization 3)

/-- n_{S⊥} seed: 12 with S={2,3} strips to 1 (12 = 2²·3, all in S).
    thm:xi-localized-quotient-index-ledger -/
theorem strip_12 : 12 / (2 ^ 2 * 3 ^ 1) = 1 := by norm_num

/-- n_{S⊥} seed: 30 with S={2,3} strips to 5 (30 = 2·3·5, keep 5).
    thm:xi-localized-quotient-index-ledger -/
theorem strip_30 : 30 / (2 ^ 1 * 3 ^ 1) = 5 := by norm_num

/-- n_{S⊥} seed: 7 with S={2,3} strips to 7 (7 coprime to 6).
    thm:xi-localized-quotient-index-ledger -/
theorem strip_7 : 7 / (2 ^ 0 * 3 ^ 0) = 7 := by norm_num

/-- n_{S⊥} seed: 60 with S={2,3} strips to 5 (60 = 2²·3·5).
    thm:xi-localized-quotient-index-ledger -/
theorem strip_60 : 60 / (2 ^ 2 * 3 ^ 1) = 5 := by norm_num

/-- n_{S⊥} seed: 35 with S={2,3} strips to 35 (35 = 5·7, both outside S).
    thm:xi-localized-quotient-index-ledger -/
theorem strip_35 : 35 / (2 ^ 0 * 3 ^ 0) = 35 := by norm_num

/-! ## p-adic valuation seeds for the stripping operation

v_p(n) gives the largest power of p dividing n. -/

/-- v_2(12) = 2 (12 = 2² · 3).
    thm:xi-localized-quotient-index-ledger -/
theorem val2_12 : Nat.factorization 12 2 = 2 := by native_decide

/-- v_3(12) = 1 (12 = 2² · 3).
    thm:xi-localized-quotient-index-ledger -/
theorem val3_12 : Nat.factorization 12 3 = 1 := by native_decide

/-- v_2(30) = 1 (30 = 2 · 3 · 5).
    thm:xi-localized-quotient-index-ledger -/
theorem val2_30 : Nat.factorization 30 2 = 1 := by native_decide

/-- v_3(30) = 1 (30 = 2 · 3 · 5).
    thm:xi-localized-quotient-index-ledger -/
theorem val3_30 : Nat.factorization 30 3 = 1 := by native_decide

/-- v_2(7) = 0 (7 is odd prime).
    thm:xi-localized-quotient-index-ledger -/
theorem val2_7 : Nat.factorization 7 2 = 0 := by native_decide

/-- v_3(7) = 0 (7 not divisible by 3).
    thm:xi-localized-quotient-index-ledger -/
theorem val3_7 : Nat.factorization 7 3 = 0 := by native_decide

/-! ## Euler totient of stripped values

For the torsion spectral count: exact-order elements number φ(n) when
all prime factors of n are outside S. -/

/-- φ(1) = 1.
    thm:xi-localized-quotient-index-ledger -/
theorem totient_1 : Nat.totient 1 = 1 := by native_decide

/-- φ(5) = 4.
    thm:xi-localized-quotient-index-ledger -/
theorem totient_5 : Nat.totient 5 = 4 := by native_decide

/-- φ(7) = 6.
    thm:xi-localized-quotient-index-ledger -/
theorem totient_7 : Nat.totient 7 = 6 := by native_decide

/-- φ(35) = 24 = φ(5)·φ(7) = 4·6 (multiplicativity for coprime arguments).
    thm:xi-localized-quotient-index-ledger -/
theorem totient_35 : Nat.totient 35 = 24 := by native_decide

/-- Totient multiplicativity seed: φ(35) = φ(5) · φ(7).
    thm:xi-localized-quotient-index-ledger -/
theorem totient_mult_5_7 : Nat.totient 35 = Nat.totient 5 * Nat.totient 7 := by native_decide

/-! ## Cyclic realization criterion seeds

Z/mZ appears as a quotient of G_S iff gcd(m, ∏_{p∈S} p^∞) = 1,
i.e., m is coprime to every prime in S. For S={2,3}: m coprime to 6. -/

/-- Coprimality seed: gcd(5, 6) = 1 (5 realizable in G_{2,3}).
    thm:xi-localized-quotient-index-ledger -/
theorem coprime_5_6 : Nat.gcd 5 6 = 1 := by native_decide

/-- Coprimality seed: gcd(7, 6) = 1 (7 realizable in G_{2,3}).
    thm:xi-localized-quotient-index-ledger -/
theorem coprime_7_6 : Nat.gcd 7 6 = 1 := by native_decide

/-- Coprimality seed: gcd(35, 6) = 1 (35 realizable in G_{2,3}).
    thm:xi-localized-quotient-index-ledger -/
theorem coprime_35_6 : Nat.gcd 35 6 = 1 := by native_decide

/-- Non-coprimality seed: gcd(4, 6) = 2 ≠ 1 (4 not realizable in G_{2,3}).
    thm:xi-localized-quotient-index-ledger -/
theorem not_coprime_4_6 : Nat.gcd 4 6 = 2 := by native_decide

/-- Non-coprimality seed: gcd(9, 6) = 3 ≠ 1 (9 not realizable in G_{2,3}).
    thm:xi-localized-quotient-index-ledger -/
theorem not_coprime_9_6 : Nat.gcd 9 6 = 3 := by native_decide

/-- Paper wrapper: Localized quotient index ledger seeds for S={2,3}.
    n_{S⊥} stripping + totient + cyclic realization criterion.
    thm:xi-localized-quotient-index-ledger -/
theorem paper_xi_localized_quotient_index_ledger_seeds :
    12 / (2 ^ 2 * 3 ^ 1) = 1 ∧ 30 / (2 ^ 1 * 3 ^ 1) = 5
    ∧ 7 / (2 ^ 0 * 3 ^ 0) = 7 ∧ 35 / (2 ^ 0 * 3 ^ 0) = 35
    ∧ Nat.totient 5 = 4 ∧ Nat.totient 7 = 6 ∧ Nat.totient 35 = 24
    ∧ Nat.gcd 5 6 = 1 ∧ Nat.gcd 7 6 = 1 ∧ Nat.gcd 4 6 = 2 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    totient_5, totient_7, totient_35, coprime_5_6, coprime_7_6, not_coprime_4_6⟩

/-- Package wrapper: Localized quotient index ledger seeds for S={2,3}.
    thm:xi-localized-quotient-index-ledger -/
theorem paper_xi_localized_quotient_index_ledger_package :
    12 / (2 ^ 2 * 3 ^ 1) = 1 ∧ 30 / (2 ^ 1 * 3 ^ 1) = 5
    ∧ 7 / (2 ^ 0 * 3 ^ 0) = 7 ∧ 35 / (2 ^ 0 * 3 ^ 0) = 35
    ∧ Nat.totient 5 = 4 ∧ Nat.totient 7 = 6 ∧ Nat.totient 35 = 24
    ∧ Nat.gcd 5 6 = 1 ∧ Nat.gcd 7 6 = 1 ∧ Nat.gcd 4 6 = 2 :=
  paper_xi_localized_quotient_index_ledger_seeds

end Omega.Zeta.QuotientIndexLedgerSeeds
