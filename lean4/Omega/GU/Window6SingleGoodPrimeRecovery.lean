import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace Omega.GU.Window6SingleGoodPrimeRecovery

open ZMod

/-- Helper: if `p ≥ 7` and `p` prime, then `p ∤ k` for `k ∈ {1, 2}`.
    Used in the distinctness lemmas below. -/
private theorem not_dvd_small (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) (k : ℕ)
    (hk_pos : 0 < k) (hk_small : k ≤ 2) : ¬ p ∣ k := by
  intro h
  have := Nat.le_of_dvd hk_pos h
  omega

/-- `2 ≠ 3` in `ZMod p` when `p` prime and `p ≥ 7`.
    thm:window6-fiber-edge-coupling-single-good-prime-recovers-multiplicity -/
theorem two_ne_three_in_zmod (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    (2 : ZMod p) ≠ 3 := by
  intro h
  have hone : (1 : ZMod p) = 0 := by linear_combination -h
  have h1 : ((1 : ℕ) : ZMod p) = 0 := by exact_mod_cast hone
  rw [ZMod.natCast_eq_zero_iff] at h1
  exact not_dvd_small p hp7 1 Nat.one_pos (by norm_num) h1

/-- `3 ≠ 4` in `ZMod p` when `p` prime and `p ≥ 7`.
    thm:window6-fiber-edge-coupling-single-good-prime-recovers-multiplicity -/
theorem three_ne_four_in_zmod (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    (3 : ZMod p) ≠ 4 := by
  intro h
  have hone : (1 : ZMod p) = 0 := by linear_combination -h
  have h1 : ((1 : ℕ) : ZMod p) = 0 := by exact_mod_cast hone
  rw [ZMod.natCast_eq_zero_iff] at h1
  exact not_dvd_small p hp7 1 Nat.one_pos (by norm_num) h1

/-- `2 ≠ 4` in `ZMod p` when `p` prime and `p ≥ 7`.
    thm:window6-fiber-edge-coupling-single-good-prime-recovers-multiplicity -/
theorem two_ne_four_in_zmod (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    (2 : ZMod p) ≠ 4 := by
  intro h
  have htwo : (2 : ZMod p) = 0 := by linear_combination -h
  have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast htwo
  rw [ZMod.natCast_eq_zero_iff] at h1
  exact not_dvd_small p hp7 2 (by norm_num) (le_refl 2) h1

/-- `6` is a unit in `ZMod p` when `p` prime and `p ≥ 7`.
    thm:window6-fiber-edge-coupling-single-good-prime-recovers-multiplicity -/
theorem six_is_unit_in_zmod (p : ℕ) [hp : Fact p.Prime] (hp7 : 7 ≤ p) :
    IsUnit (6 : ZMod p) := by
  have : (ZMod p) = (ZMod p) := rfl
  have hfield : Fact p.Prime := hp
  have : IsUnit (6 : ZMod p) ↔ (6 : ZMod p) ≠ 0 := by
    haveI : Fact p.Prime := hp
    exact isUnit_iff_ne_zero
  rw [this]
  intro h
  have h6 : ((6 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h6
  have := Nat.le_of_dvd (by norm_num) h6
  omega

/-- Triple distinctness.
    thm:window6-fiber-edge-coupling-single-good-prime-recovers-multiplicity -/
theorem two_three_four_distinct_in_zmod (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    (2 : ZMod p) ≠ 3 ∧ (2 : ZMod p) ≠ 4 ∧ (3 : ZMod p) ≠ 4 :=
  ⟨two_ne_three_in_zmod p hp7,
   two_ne_four_in_zmod p hp7,
   three_ne_four_in_zmod p hp7⟩

/-- Recovery: if `n, m ∈ {2,3,4}` and `n ≡ m (mod p)` for good `p`, then `n = m`.
    thm:window6-fiber-edge-coupling-single-good-prime-recovers-multiplicity -/
theorem nat_recoverable_from_zmod
    (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (n m : ℕ) (hn : n ∈ ({2, 3, 4} : Set ℕ)) (hm : m ∈ ({2, 3, 4} : Set ℕ))
    (heq : (n : ZMod p) = (m : ZMod p)) :
    n = m := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn hm
  rcases hn with rfl | rfl | rfl <;> rcases hm with rfl | rfl | rfl
  all_goals first
    | rfl
    | (exfalso; revert heq; push_cast; intro heq
       first
         | exact two_ne_three_in_zmod p hp7 heq
         | exact two_ne_four_in_zmod p hp7 heq
         | exact three_ne_four_in_zmod p hp7 heq
         | exact (two_ne_three_in_zmod p hp7) heq.symm
         | exact (two_ne_four_in_zmod p hp7) heq.symm
         | exact (three_ne_four_in_zmod p hp7) heq.symm)

/-- Paper package.
    thm:window6-fiber-edge-coupling-single-good-prime-recovers-multiplicity -/
theorem paper_window6_fiber_edge_coupling_single_good_prime_recovers_multiplicity
    (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (n m : ℕ) (hn : n ∈ ({2, 3, 4} : Set ℕ)) (hm : m ∈ ({2, 3, 4} : Set ℕ))
    (heq : (n : ZMod p) = (m : ZMod p)) :
    n = m :=
  nat_recoverable_from_zmod p hp7 n m hn hm heq

end Omega.GU.Window6SingleGoodPrimeRecovery
