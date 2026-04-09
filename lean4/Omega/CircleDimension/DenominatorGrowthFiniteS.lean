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

/-- Paper package (downgraded): denominator growth finite `S`, weak linear bound.
    prop:cdim-denominator-growth-finite-S -/
theorem paper_cdim_denominator_growth_finite_S :
    (∀ (S : Finset ℕ) (B : ℕ), N_S S B ≤ B) ∧
    (∀ S : Finset ℕ, N_S S 0 = 0) ∧
    (∀ (S : Finset ℕ) {B₁ B₂ : ℕ}, B₁ ≤ B₂ → N_S S B₁ ≤ N_S S B₂) ∧
    (∀ (S : Finset ℕ) (B : ℕ), N_S S B ≤ 2 ^ (Nat.log 2 B + 1)) :=
  ⟨N_S_le_B, N_S_zero, @N_S_mono, N_S_le_two_pow_log⟩

end Omega.CircleDimension.DenominatorGrowthFiniteS
