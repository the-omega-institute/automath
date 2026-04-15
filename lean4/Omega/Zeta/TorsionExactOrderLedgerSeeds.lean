import Mathlib.Tactic

/-!
# Torsion exact-order ledger and Pontryagin dual n-torsion seeds

For the localized number system G_S and its Pontryagin dual Σ_S = Ĝ_S,
the n-torsion subgroup satisfies:
  |Σ_S[n]| = n_{S⊥}
where n_{S⊥} = n / ∏_{p∈S} p^{v_p(n)} is the S-coprime part.

The exact-order count is:
  #{x ∈ Σ_S : ord(x) = n} = φ(n)  if all prime factors of n are outside S
                              = 0    otherwise

## Seed values

The Euler totient φ(n) at small values:
- φ(1) = 1, φ(2) = 1, φ(3) = 2, φ(4) = 2, φ(5) = 4, φ(6) = 2

The S-coprime part n_{S⊥} for S = {2, 3}:
- 12_{S⊥} = 12 / (4·3) = 1
- 30_{S⊥} = 30 / (2·3) = 5
- 7_{S⊥} = 7 (no S-primes divide 7)

The exact-order Dirichlet series E_S(s) = ζ(s-1)/ζ(s) · ∏_{p∈S} correction.

## Paper references

- thm:xi-localized-torsion-exact-order-ledger
-/

namespace Omega.Zeta.TorsionExactOrderLedgerSeeds

/-! ## Euler totient seeds

The function φ(n) = n · ∏_{p|n}(1 - 1/p) gives the count of units in ℤ/nℤ. -/

/-- Euler totient at small values via Nat.totient.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem totient_1 : Nat.totient 1 = 1 := by native_decide

/-- Euler totient seed: φ(2) = 1.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem totient_2 : Nat.totient 2 = 1 := by native_decide

/-- Euler totient seed: φ(3) = 2.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem totient_3 : Nat.totient 3 = 2 := by native_decide

/-- Euler totient seed: φ(4) = 2.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem totient_4 : Nat.totient 4 = 2 := by native_decide

/-- Euler totient seed: φ(5) = 4.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem totient_5 : Nat.totient 5 = 4 := by native_decide

/-- Euler totient seed: φ(6) = 2.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem totient_6 : Nat.totient 6 = 2 := by native_decide

/-- Euler totient seed: φ(7) = 6.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem totient_7 : Nat.totient 7 = 6 := by native_decide

/-- Euler totient seed: φ(12) = 4.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem totient_12 : Nat.totient 12 = 4 := by native_decide

/-! ## S-coprime stripping function: n_{S⊥}

For S = {2, 3}, the S-coprime part strips all factors of 2 and 3 from n.
At integer level, we verify this via explicit division. -/

/-- Strip all factors of p from n (p-adic valuation removal).
    thm:xi-localized-torsion-exact-order-ledger -/
def stripPrime (p n : ℕ) : ℕ :=
  n / p ^ (Nat.log p n + 1) * p ^ (Nat.log p n + 1)
  |> fun _ => n / p ^ n.factorization p

/-- S-coprime part for S = {2, 3}: strip 2-adic and 3-adic parts.
    thm:xi-localized-torsion-exact-order-ledger -/
def sCoprimePart23 (n : ℕ) : ℕ :=
  n / (2 ^ n.factorization 2 * 3 ^ n.factorization 3)

/-- S-coprime part seed: 12_{S⊥} = 1 for S = {2,3}.
    12 = 2² · 3, so 12_{S⊥} = 12/12 = 1.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem sCoprime_12 : sCoprimePart23 12 = 1 := by native_decide

/-- S-coprime part seed: 30_{S⊥} = 5 for S = {2,3}.
    30 = 2 · 3 · 5, so 30_{S⊥} = 30/6 = 5.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem sCoprime_30 : sCoprimePart23 30 = 5 := by native_decide

/-- S-coprime part seed: 7_{S⊥} = 7 for S = {2,3}.
    7 is coprime to both 2 and 3.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem sCoprime_7 : sCoprimePart23 7 = 7 := by native_decide

/-- S-coprime part seed: 60_{S⊥} = 5 for S = {2,3}.
    60 = 2² · 3 · 5, so 60_{S⊥} = 60/12 = 5.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem sCoprime_60 : sCoprimePart23 60 = 5 := by native_decide

/-- S-coprime part seed: 35_{S⊥} = 35 for S = {2,3}.
    35 = 5 · 7, coprime to both 2 and 3.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem sCoprime_35 : sCoprimePart23 35 = 35 := by native_decide

/-! ## Euler factor seeds for the exact-order Dirichlet series

For p ∉ S, the Euler factor of E_S(s) is (1-p^{-s})/(1-p^{1-s}).
At s=2: (1-1/p²)/(1-1/p) = (p²-1)/(p(p-1)) = (p+1)/p.

For p ∈ S, the Euler factor is 1 (trivial). -/

/-- Euler factor numerator (p²-1) at s=2 for primes not in S.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem euler_factor_num_5 : 5 ^ 2 - 1 = 24 := by norm_num

/-- Euler factor numerator for p=7.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem euler_factor_num_7 : 7 ^ 2 - 1 = 48 := by norm_num

/-- Euler factor denominator p(p-1) at s=2 for p=5.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem euler_factor_denom_5 : 5 * (5 - 1) = 20 := by norm_num

/-- Euler factor denominator p(p-1) at s=2 for p=7.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem euler_factor_denom_7 : 7 * (7 - 1) = 42 := by norm_num

/-! ## Prime power totient identity: φ(p^e) = p^e - p^{e-1}

This is the key identity used in computing Euler factors. -/

/-- Prime power totient seed: φ(4) = 4 - 2 = 2.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem totient_pow_2_2 : Nat.totient (2 ^ 2) = 2 ^ 2 - 2 ^ 1 := by native_decide

/-- Prime power totient seed: φ(8) = 8 - 4 = 4.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem totient_pow_2_3 : Nat.totient (2 ^ 3) = 2 ^ 3 - 2 ^ 2 := by native_decide

/-- Prime power totient seed: φ(9) = 9 - 3 = 6.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem totient_pow_3_2 : Nat.totient (3 ^ 2) = 3 ^ 2 - 3 ^ 1 := by native_decide

/-- Prime power totient seed: φ(25) = 25 - 5 = 20.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem totient_pow_5_2 : Nat.totient (5 ^ 2) = 5 ^ 2 - 5 ^ 1 := by native_decide

/-- Prime power totient seed: φ(27) = 27 - 9 = 18.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem totient_pow_3_3 : Nat.totient (3 ^ 3) = 3 ^ 3 - 3 ^ 2 := by native_decide

/-- Paper wrapper: Torsion exact-order ledger seeds.
    Euler totient values, S-coprime stripping for S={2,3},
    and prime power totient identity φ(p^e) = p^e - p^{e-1}.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem paper_xi_torsion_exact_order_ledger_seeds :
    Nat.totient 1 = 1 ∧ Nat.totient 5 = 4 ∧ Nat.totient 7 = 6
    ∧ sCoprimePart23 12 = 1 ∧ sCoprimePart23 30 = 5 ∧ sCoprimePart23 7 = 7
    ∧ Nat.totient (2 ^ 2) = 2 ^ 2 - 2 ^ 1
    ∧ Nat.totient (3 ^ 2) = 3 ^ 2 - 3 ^ 1 := by
  exact ⟨totient_1, totient_5, totient_7,
    sCoprime_12, sCoprime_30, sCoprime_7,
    totient_pow_2_2, totient_pow_3_2⟩

/-- Packaged form of the torsion exact-order ledger seeds.
    thm:xi-localized-torsion-exact-order-ledger -/
theorem paper_xi_torsion_exact_order_ledger_package :
    Nat.totient 1 = 1 ∧ Nat.totient 5 = 4 ∧ Nat.totient 7 = 6
    ∧ sCoprimePart23 12 = 1 ∧ sCoprimePart23 30 = 5 ∧ sCoprimePart23 7 = 7
    ∧ Nat.totient (2 ^ 2) = 2 ^ 2 - 2 ^ 1
    ∧ Nat.totient (3 ^ 2) = 3 ^ 2 - 3 ^ 1 :=
  paper_xi_torsion_exact_order_ledger_seeds

end Omega.Zeta.TorsionExactOrderLedgerSeeds
