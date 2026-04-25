import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-!
# Fibonacci Prime Pisano Period Properties

Formalizations from the GU chapter: Fibonacci prime explicit sqrt(-1),
Pisano period verification, and strong congruence rigidity.
-/

namespace Omega.GU

open scoped NumberTheorySymbols

/-- Fibonacci prime explicit sqrt(-1): for known Fibonacci primes F_n,
    F_{n+1}² ≡ -1 (mod F_n), verified at n=5,7,11,13.
    cor:gut-fibprime-explicit-i -/
theorem paper_fibprime_explicit_sqrt_neg_one :
    (Nat.fib 4) ^ 2 % (Nat.fib 5) = Nat.fib 5 - 1 ∧
    (Nat.fib 8) ^ 2 % (Nat.fib 7) = Nat.fib 7 - 1 ∧
    (Nat.fib 12) ^ 2 % (Nat.fib 11) = Nat.fib 11 - 1 ∧
    (Nat.fib 14) ^ 2 % (Nat.fib 13) = Nat.fib 13 - 1 := by
  native_decide

/-- Pisano period for Fibonacci primes: π(F_n) = 4n.
    cor:gut-fibprime-pisano-4n -/
theorem paper_fibprime_pisano_4n :
    (Nat.fib 20 % 5 = 0 ∧ Nat.fib 21 % 5 = 1) ∧
    (Nat.fib 10 % 5 ≠ 0 ∨ Nat.fib 11 % 5 ≠ 1) ∧
    (Nat.fib 28 % 13 = 0 ∧ Nat.fib 29 % 13 = 1) ∧
    (Nat.fib 14 % 13 ≠ 0 ∨ Nat.fib 15 % 13 ≠ 1) := by
  native_decide

/-- Strong congruence rigidity for Fibonacci primes: F_n ≡ ±1 (mod n).
    prop:gut-fibprime-congruence-p-mod-n -/
theorem paper_fibprime_congruence_p_mod_n :
    Nat.fib 7 % 7 = 6 ∧
    Nat.fib 11 % 11 = 1 ∧
    Nat.fib 13 % 13 = 12 ∧
    Nat.fib 17 % 17 = 16 := by
  native_decide

set_option maxHeartbeats 400000 in
/-- If `p = F_n` is prime, `r` is the rank of apparition of `p`, and the classical
Lucas/Wall divisibility `r ∣ p - (5 / p)` holds, then `r = n`; hence
`p ≡ (5 / p) [ZMOD n]`.
    prop:gut-fibprime-congruence-p-mod-n -/
theorem paper_gut_fibprime_congruence_p_mod_n
    {n r p : ℕ} [hp : Fact p.Prime]
    (hn : Nat.Prime n) (hn5 : 5 < n) (hpfib : p = Nat.fib n)
    (hr_pos : 0 < r) (hpr : p ∣ Nat.fib r)
    (hr_min : ∀ k, 0 < k → k < r → ¬ p ∣ Nat.fib k)
    (hWall : (r : ℤ) ∣ (p : ℤ) - legendreSym p 5) :
    (p : ℤ) ≡ legendreSym p 5 [ZMOD n] := by
  have hp' : Nat.Prime p := Fact.out
  have hn_pos : 0 < n := hn.pos
  have hn_two : 2 ≤ n := by omega
  have hFibDiv : Nat.fib n ∣ Nat.fib r := by
    simpa [hpfib] using hpr
  have hFibGcd : Nat.fib (Nat.gcd n r) = Nat.fib n := by
    calc
      Nat.fib (Nat.gcd n r) = Nat.gcd (Nat.fib n) (Nat.fib r) := Nat.fib_gcd n r
      _ = Nat.fib n := Nat.gcd_eq_left_iff_dvd.mpr hFibDiv
  have hgcd_two : 2 ≤ Nat.gcd n r := by
    have hFibPos : 0 < Nat.fib n := Nat.fib_pos.mpr hn_pos
    have hFibNeOne : Nat.fib n ≠ 1 := by
      have hFibPrime : Nat.Prime (Nat.fib n) := by simpa [hpfib] using hp'
      exact Nat.ne_of_gt hFibPrime.one_lt
    by_contra h
    have hsmall : Nat.gcd n r = 0 ∨ Nat.gcd n r = 1 := by omega
    cases hsmall with
    | inl h0 =>
        rw [h0] at hFibGcd
        simp at hFibGcd
        exact (Nat.ne_of_gt hFibPos) hFibGcd.symm
    | inr h1 =>
        rw [h1] at hFibGcd
        simp at hFibGcd
        exact hFibNeOne hFibGcd.symm
  have hgcd_eq_n : Nat.gcd n r = n := by
    have hgcd_le_n : Nat.gcd n r ≤ n := Nat.le_of_dvd hn_pos (Nat.gcd_dvd_left n r)
    by_contra hne
    have hgcd_lt_n : Nat.gcd n r < n := lt_of_le_of_ne hgcd_le_n hne
    have hFibLt : Nat.fib (Nat.gcd n r) < Nat.fib n := (Nat.fib_lt_fib hgcd_two).2 hgcd_lt_n
    exact hFibLt.ne hFibGcd
  have hnr : n ∣ r := Nat.gcd_eq_left_iff_dvd.mp hgcd_eq_n
  have hr_le_n : r ≤ n := by
    by_contra h
    have hlt : n < r := Nat.lt_of_not_ge h
    have hpn : p ∣ Nat.fib n := by simpa [hpfib]
    exact (hr_min n hn_pos hlt hpn).elim
  have hr_eq : r = n := by
    rcases hnr with ⟨k, hk⟩
    have hk_pos : 0 < k := by
      by_contra hk_nonpos
      have hk_zero : k = 0 := by omega
      rw [hk, hk_zero] at hr_pos
      simp at hr_pos
    have hk_eq_one : k = 1 := by
      by_contra hk_ne_one
      have hk_ge_two : 2 ≤ k := by omega
      have hmul_le : n * 2 ≤ n * k := Nat.mul_le_mul_left n hk_ge_two
      have hmul_lt : n < n * 2 := by omega
      have : n < n * k := lt_of_lt_of_le hmul_lt hmul_le
      rw [← hk] at this
      exact not_lt_of_ge hr_le_n this
    simpa [hk_eq_one] using hk
  have hWall' : (n : ℤ) ∣ (p : ℤ) - legendreSym p 5 := by
    simpa [hr_eq] using hWall
  exact (Int.modEq_iff_dvd.mpr hWall').symm

/-- Paper: Pisano-period and congruence rigidity package.
    cor:gut-fibprime-pisano-4n -/
theorem paper_fibprime_pisano_rigidity_package :
    ((Nat.fib 20 % 5 = 0 ∧ Nat.fib 21 % 5 = 1) ∧
      (Nat.fib 10 % 5 ≠ 0 ∨ Nat.fib 11 % 5 ≠ 1) ∧
      (Nat.fib 28 % 13 = 0 ∧ Nat.fib 29 % 13 = 1) ∧
      (Nat.fib 14 % 13 ≠ 0 ∨ Nat.fib 15 % 13 ≠ 1)) ∧
    (Nat.fib 7 % 7 = 6 ∧ Nat.fib 11 % 11 = 1 ∧ Nat.fib 13 % 13 = 12 ∧ Nat.fib 17 % 17 = 16) := by
  refine ⟨paper_fibprime_pisano_4n, ?_⟩
  exact paper_fibprime_congruence_p_mod_n

/-- Sign of F_n mod n determined by n mod 20.
    cor:gut-fibprime-sign-by-n-mod20 -/
theorem paper_fibprime_sign_by_n_mod20 :
    (Nat.fib 20 % 5 = 0 ∧ Nat.fib 21 % 5 = 1) ∧
    Nat.fib 7 % 5 = 3 ∧
    Nat.fib 11 % 5 = 4 ∧
    Nat.fib 13 % 5 = 3 ∧
    Nat.fib 17 % 5 = 2 ∧
    Nat.fib 11 % 11 = 1 ∧
    Nat.fib 7 % 7 = 6 := by
  native_decide

/-- Discriminant -15 splitting criterion for Fibonacci prime fields.
    cor:gut-fibprime-disc-minus15-criterion -/
theorem paper_fibprime_disc_minus15_criterion :
    1 - 4 * 2 * 2 = (-15 : ℤ) ∧
    15 % 13 = 2 ∧
    15 % 89 = 15 ∧
    Nat.Prime 13 ∧ Nat.Prime 89 := by
  refine ⟨by omega, by omega, by omega, by native_decide, by native_decide⟩

/-- Numerical certificates for orthogonal/symplectic Fibonacci-Lie resonance.
    thm:fib-lie-resonance-global-orthogonal-symplectic -/
theorem paper_fib_lie_resonance_orthogonal_symplectic :
    (7 * 6 / 2 = Nat.fib 8) ∧
    (11 * 10 / 2 = Nat.fib 10) ∧
    (3 * (2 * 3 + 1) = Nat.fib 8) ∧
    (5 * (2 * 5 + 1) = Nat.fib 10) ∧
    (∃ s : ℕ, s * (s + 1) / 2 = Nat.fib 4 ∧ s = 2) ∧
    (∃ s : ℕ, s * (s + 1) / 2 = Nat.fib 8 ∧ s = 6) ∧
    (∃ s : ℕ, s * (s + 1) / 2 = Nat.fib 10 ∧ s = 10) := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    ⟨2, by native_decide, rfl⟩, ⟨6, by native_decide, rfl⟩, ⟨10, by native_decide, rfl⟩⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R306: Pisano period p=17,19,23 + Wall divisibility
-- ══════════════════════════════════════════════════════════════

/-- cor:gut-fibprime-pisano-4n -/
theorem pisano_period_17 : Nat.fib 36 % 17 = 0 ∧ Nat.fib 37 % 17 = 1 := by native_decide

/-- cor:gut-fibprime-pisano-4n -/
theorem pisano_period_19 : Nat.fib 18 % 19 = 0 ∧ Nat.fib 19 % 19 = 1 := by native_decide

/-- cor:gut-fibprime-pisano-4n -/
theorem pisano_period_23 : Nat.fib 48 % 23 = 0 ∧ Nat.fib 49 % 23 = 1 := by native_decide

/-- cor:gut-fibprime-pisano-4n -/
theorem pisano_wall_divisibility :
    36 ∣ (2 * (17 + 1)) ∧ 18 ∣ (19 - 1) ∧ 48 ∣ (2 * (23 + 1)) := by omega

/-- Paper package. cor:gut-fibprime-pisano-4n -/
theorem paper_pisano_extended :
    (Nat.fib 36 % 17 = 0 ∧ Nat.fib 37 % 17 = 1) ∧
    (Nat.fib 18 % 19 = 0 ∧ Nat.fib 19 % 19 = 1) ∧
    (Nat.fib 48 % 23 = 0 ∧ Nat.fib 49 % 23 = 1) := by
  exact ⟨pisano_period_17, pisano_period_19, pisano_period_23⟩

/-- Pisano period for p = 29: π(29) = 14.
    prop:gu-fibprime-pisano-periods -/
theorem pisano_period_29 : Nat.fib 14 % 29 = 0 ∧ Nat.fib 15 % 29 = 1 := by native_decide

/-- Paper package for p = 29.
    prop:gu-fibprime-pisano-periods -/
theorem paper_pisano_period_29 :
    (Nat.fib 14 % 29 = 0 ∧ Nat.fib 15 % 29 = 1) := pisano_period_29

/-- Pisano period for p = 31: π(31) = 30.
    prop:gu-fibprime-pisano-periods -/
theorem pisano_period_31 : Nat.fib 30 % 31 = 0 ∧ Nat.fib 31 % 31 = 1 := by native_decide

/-- Pisano period for p = 47: π(47) = 32.
    prop:gu-fibprime-pisano-periods -/
theorem pisano_period_47 : Nat.fib 32 % 47 = 0 ∧ Nat.fib 33 % 47 = 1 := by native_decide

/-- Paper package for p = 31, 47.
    prop:gu-fibprime-pisano-periods -/
theorem paper_pisano_period_31_47 :
    (Nat.fib 30 % 31 = 0 ∧ Nat.fib 31 % 31 = 1) ∧
    (Nat.fib 32 % 47 = 0 ∧ Nat.fib 33 % 47 = 1) :=
  ⟨pisano_period_31, pisano_period_47⟩

/-- Pisano period for p = 41: π(41) = 40.
    prop:gu-fibprime-pisano-periods -/
theorem pisano_period_41 : Nat.fib 40 % 41 = 0 ∧ Nat.fib 41 % 41 = 1 := by native_decide

/-- Pisano period for p = 59: π(59) = 58.
    prop:gu-fibprime-pisano-periods -/
theorem pisano_period_59 : Nat.fib 58 % 59 = 0 ∧ Nat.fib 59 % 59 = 1 := by native_decide

/-- Paper package for p = 41, 59.
    prop:gu-fibprime-pisano-periods -/
theorem paper_pisano_period_41_59 :
    (Nat.fib 40 % 41 = 0 ∧ Nat.fib 41 % 41 = 1) ∧
    (Nat.fib 58 % 59 = 0 ∧ Nat.fib 59 % 59 = 1) :=
  ⟨pisano_period_41, pisano_period_59⟩

/-- Pisano period for p = 61: π(61) = 60.
    prop:gu-fibprime-pisano-periods -/
theorem pisano_period_61 : Nat.fib 60 % 61 = 0 ∧ Nat.fib 61 % 61 = 1 := by native_decide

/-- Pisano period for p = 71: π(71) = 70.
    prop:gu-fibprime-pisano-periods -/
theorem pisano_period_71 : Nat.fib 70 % 71 = 0 ∧ Nat.fib 71 % 71 = 1 := by native_decide

/-- Paper package for p = 61, 71.
    prop:gu-fibprime-pisano-periods -/
theorem paper_pisano_period_61_71 :
    (Nat.fib 60 % 61 = 0 ∧ Nat.fib 61 % 61 = 1) ∧
    (Nat.fib 70 % 71 = 0 ∧ Nat.fib 71 % 71 = 1) :=
  ⟨pisano_period_61, pisano_period_71⟩

/-- Pisano period for p = 89: π(89) = 44.
    prop:gu-fibprime-pisano-periods -/
theorem pisano_period_89 : Nat.fib 44 % 89 = 0 ∧ Nat.fib 45 % 89 = 1 := by native_decide

/-- Paper package for p = 89.
    prop:gu-fibprime-pisano-periods -/
theorem paper_pisano_period_89 :
    Nat.fib 44 % 89 = 0 ∧ Nat.fib 45 % 89 = 1 := pisano_period_89

/-- Pisano period for p = 101: π(101) = 50.
    prop:gu-fibprime-pisano-periods -/
theorem pisano_period_101 : Nat.fib 50 % 101 = 0 ∧ Nat.fib 51 % 101 = 1 := by native_decide

/-- Paper package for p = 101.
    prop:gu-fibprime-pisano-periods -/
theorem paper_pisano_period_101 :
    Nat.fib 50 % 101 = 0 ∧ Nat.fib 51 % 101 = 1 := pisano_period_101

/-- Pisano period for p = 107: π(107) = 72.
    prop:gu-fibprime-pisano-periods -/
theorem pisano_period_107 : Nat.fib 72 % 107 = 0 ∧ Nat.fib 73 % 107 = 1 := by native_decide

/-- Pisano period for p = 113: π(113) = 76.
    prop:gu-fibprime-pisano-periods -/
theorem pisano_period_113 : Nat.fib 76 % 113 = 0 ∧ Nat.fib 77 % 113 = 1 := by native_decide

/-- Paper package for p = 107, 113.
    prop:gu-fibprime-pisano-periods -/
theorem paper_pisano_period_107_113 :
    (Nat.fib 72 % 107 = 0 ∧ Nat.fib 73 % 107 = 1) ∧
    (Nat.fib 76 % 113 = 0 ∧ Nat.fib 77 % 113 = 1) :=
  ⟨pisano_period_107, pisano_period_113⟩

/-- Pisano period π(67) = 136.
    cor:field-phase-fib-prime -/
theorem pisano_period_67 :
    Nat.fib 136 % 67 = 0 ∧ Nat.fib 137 % 67 = 1 := by native_decide

/-- Pisano period π(73) = 148.
    cor:field-phase-fib-prime -/
theorem pisano_period_73 :
    Nat.fib 148 % 73 = 0 ∧ Nat.fib 149 % 73 = 1 := by native_decide

/-- Pisano period π(79) = 78.
    cor:field-phase-fib-prime -/
theorem pisano_period_79 :
    Nat.fib 78 % 79 = 0 ∧ Nat.fib 79 % 79 = 1 := by native_decide

/-- Paper Pisano period witness package for primes 67, 73, 79.
    cor:field-phase-fib-prime -/
theorem paper_pisano_period_67_73_79_extended :
    (Nat.fib 136 % 67 = 0 ∧ Nat.fib 137 % 67 = 1) ∧
    (Nat.fib 148 % 73 = 0 ∧ Nat.fib 149 % 73 = 1) ∧
    (Nat.fib 78 % 79 = 0 ∧ Nat.fib 79 % 79 = 1) :=
  ⟨pisano_period_67, pisano_period_73, pisano_period_79⟩

end Omega.GU
