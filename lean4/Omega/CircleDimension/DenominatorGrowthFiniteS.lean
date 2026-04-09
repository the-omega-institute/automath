import Mathlib.Tactic
import Mathlib.Data.Nat.Log

namespace Omega.CircleDimension.DenominatorGrowthFiniteS

open Nat Finset
open scoped Classical

/-- Count of integers in `[1,B]` whose prime factors all lie in `S`.
    prop:cdim-denominator-growth-finite-S -/
noncomputable def N_S (S : Finset ℕ) (B : ℕ) : ℕ :=
  ((Finset.Icc 1 B).filter (fun n =>
    ∀ p, p.Prime → p ∣ n → p ∈ S)).card

/-- Exponent bound: if `p^e ≤ B`, then `e ≤ Nat.log p B`.
    prop:cdim-denominator-growth-finite-S -/
theorem exponent_le_log (p B e : ℕ) (hp : 2 ≤ p) (he : p ^ e ≤ B) :
    e ≤ Nat.log p B := by
  have : Nat.log p (p ^ e) ≤ Nat.log p B := Nat.log_mono_right he
  rwa [Nat.log_pow hp] at this

/-- Weak bound: `N_S S B ≤ B` (filter ⊆ `Icc 1 B`, whose card is `B`).
    prop:cdim-denominator-growth-finite-S -/
theorem N_S_le_B (S : Finset ℕ) (B : ℕ) : N_S S B ≤ B := by
  unfold N_S
  have h1 : ((Finset.Icc 1 B).filter
      (fun n => ∀ p, p.Prime → p ∣ n → p ∈ S)).card ≤ (Finset.Icc 1 B).card :=
    Finset.card_filter_le _ _
  have h2 : (Finset.Icc 1 B).card ≤ B := by
    rw [Nat.card_Icc]
    omega
  omega

/-- Trivial zero case: `N_S S 0 = 0`.
    prop:cdim-denominator-growth-finite-S -/
theorem N_S_zero (S : Finset ℕ) : N_S S 0 = 0 := by
  have h := N_S_le_B S 0
  omega

/-- Monotonicity in `B`: `B₁ ≤ B₂ → N_S S B₁ ≤ N_S S B₂`.
    prop:cdim-denominator-growth-finite-S -/
theorem N_S_mono (S : Finset ℕ) {B₁ B₂ : ℕ} (hB : B₁ ≤ B₂) :
    N_S S B₁ ≤ N_S S B₂ := by
  unfold N_S
  apply Finset.card_le_card
  apply Finset.monotone_filter_left
  intro n hn
  simp only [Finset.mem_Icc] at hn ⊢
  exact ⟨hn.1, hn.2.trans hB⟩

/-- Log-linear weak bound: `N_S S B ≤ B ≤ 2^(Nat.log 2 B + 1)` (for `B ≥ 1`).
    prop:cdim-denominator-growth-finite-S -/
theorem N_S_le_two_pow_log (S : Finset ℕ) (B : ℕ) :
    N_S S B ≤ 2 ^ (Nat.log 2 B + 1) := by
  have h1 : N_S S B ≤ B := N_S_le_B S B
  have h2 : B < 2 ^ (Nat.log 2 B + 1) := Nat.lt_pow_succ_log_self (by norm_num) B
  omega

/-- Two S-smooth positive numbers with the same factorization on S are equal.
    prop:cdim-denominator-growth-finite-S -/
theorem factorization_injOn_smooth (S : Finset ℕ) (B : ℕ) :
    Set.InjOn (fun n (p : ℕ) (_ : p ∈ S) => n.factorization p)
      ((Finset.Icc 1 B).filter (fun n => ∀ p, p.Prime → p ∣ n → p ∈ S) : Set ℕ) := by
  intro a ha b hb heq
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at ha hb
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  rw [← Nat.factorization_prod_pow_eq_self ha0, ← Nat.factorization_prod_pow_eq_self hb0]
  congr 1; ext p
  by_cases hp : p.Prime
  · by_cases hpa : p ∣ a
    · have hpS : p ∈ S := ha.2 p hp hpa
      exact congr_fun (congr_fun heq p) hpS
    · by_cases hpb : p ∣ b
      · have hpS : p ∈ S := hb.2 p hp hpb
        exact congr_fun (congr_fun heq p) hpS
      · rw [Nat.factorization_eq_zero_of_not_dvd hpa,
            Nat.factorization_eq_zero_of_not_dvd hpb]
  · rw [Nat.factorization_eq_zero_of_not_prime a hp,
        Nat.factorization_eq_zero_of_not_prime b hp]

/-- Exponent bound on factorization for numbers in [1,B].
    prop:cdim-denominator-growth-finite-S -/
theorem factorization_lt_log_succ {n p B : ℕ} (hn : n ∈ Finset.Icc 1 B)
    (hp : 2 ≤ p) : n.factorization p < Nat.log p B + 1 := by
  simp only [Finset.mem_Icc] at hn
  by_cases hpp : p.Prime
  · have hfact : p ^ n.factorization p ∣ n := by
      rw [Nat.factorization_def n hpp]; exact pow_padicValNat_dvd
    have hle : p ^ n.factorization p ≤ B :=
      le_trans (Nat.le_of_dvd (by omega) hfact) hn.2
    exact Nat.lt_succ_of_le (exponent_le_log p B (n.factorization p) hp hle)
  · rw [Nat.factorization_eq_zero_of_not_prime n hpp]; omega

/-- Product bound: `N_S(S, B) ≤ ∏_{p ∈ S} (log_p(B) + 1)`.
    prop:cdim-denominator-growth-finite-S -/
theorem N_S_le_prod_log (S : Finset ℕ) (B : ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    N_S S B ≤ ∏ p ∈ S, (Nat.log p B + 1) := by
  unfold N_S
  calc ((Finset.Icc 1 B).filter (fun n =>
      ∀ p, p.Prime → p ∣ n → p ∈ S)).card
      ≤ (S.pi (fun p => Finset.range (Nat.log p B + 1))).card := by
        apply Finset.card_le_card_of_injOn
          (fun n (p : ℕ) (_ : p ∈ S) => n.factorization p)
        · intro n hn
          simp only [Finset.mem_coe, Finset.mem_pi, Finset.mem_range]
          intro p hp
          exact factorization_lt_log_succ (Finset.mem_of_mem_filter n hn) (hS p hp)
        · exact factorization_injOn_smooth S B
    _ = ∏ p ∈ S, (Nat.log p B + 1) := by
        rw [Finset.card_pi]; congr 1; ext p; exact Finset.card_range _

/-- Power bound: `N_S(S, B) ≤ (log₂(B) + 1) ^ |S|`.
    prop:cdim-denominator-growth-finite-S -/
theorem N_S_le_log2_pow_card (S : Finset ℕ) (B : ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    N_S S B ≤ (Nat.log 2 B + 1) ^ S.card := by
  calc N_S S B
      ≤ ∏ p ∈ S, (Nat.log p B + 1) := N_S_le_prod_log S B hS
    _ ≤ ∏ _p ∈ S, (Nat.log 2 B + 1) := by
        apply Finset.prod_le_prod
        · intro p _; omega
        · intro p hp
          have : Nat.log p B ≤ Nat.log 2 B :=
            Nat.log_anti_left (by omega : (1 : ℕ) < 2) (hS p hp)
          omega
    _ = (Nat.log 2 B + 1) ^ S.card := Finset.prod_const _

/-- Paper package: denominator growth finite `S`, product and power bounds.
    prop:cdim-denominator-growth-finite-S -/
theorem paper_cdim_denominator_growth_finite_S :
    (∀ (S : Finset ℕ) (B : ℕ), N_S S B ≤ B) ∧
    (∀ S : Finset ℕ, N_S S 0 = 0) ∧
    (∀ (S : Finset ℕ) {B₁ B₂ : ℕ}, B₁ ≤ B₂ → N_S S B₁ ≤ N_S S B₂) ∧
    (∀ (S : Finset ℕ) (B : ℕ), N_S S B ≤ 2 ^ (Nat.log 2 B + 1)) ∧
    (∀ (S : Finset ℕ) (B : ℕ), (∀ p ∈ S, 2 ≤ p) →
      N_S S B ≤ ∏ p ∈ S, (Nat.log p B + 1)) ∧
    (∀ (S : Finset ℕ) (B : ℕ), (∀ p ∈ S, 2 ≤ p) →
      N_S S B ≤ (Nat.log 2 B + 1) ^ S.card) :=
  ⟨N_S_le_B, N_S_zero, @N_S_mono, N_S_le_two_pow_log, N_S_le_prod_log, N_S_le_log2_pow_card⟩

end Omega.CircleDimension.DenominatorGrowthFiniteS
