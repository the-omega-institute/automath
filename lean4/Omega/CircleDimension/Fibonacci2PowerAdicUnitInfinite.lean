import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.CircleDimension.OddDivisibilityTowerHolographicSeparation
import Omega.Folding.ShiftDynamics

namespace Omega.CircleDimension

private lemma three_not_dvd_two_pow (k : ℕ) : ¬ 3 ∣ 2 ^ k := by
  intro h
  have hthree : 3 ∣ 2 := (by decide : Nat.Prime 3).dvd_of_dvd_pow h
  omega

private lemma lucas_two_pow_gt_one (k : ℕ) : 1 < Omega.lucasNum (2 ^ (k + 2)) := by
  have hn : 1 ≤ 2 ^ (k + 2) := Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) _)
  have hkm1 : 1 ≤ 2 ^ (k + 2) - 1 := by
    have hpow : 2 ≤ 2 ^ (k + 2) := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 2) := by
          exact Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hFib' : 1 < Nat.fib ((2 ^ (k + 2) - 1) + 2) :=
    Omega.fib_gt_one_of_ge_two (m := 2 ^ (k + 2) - 1) hkm1
  have hFib : 1 < Nat.fib (2 ^ (k + 2) + 1) := by
    have hidx : (2 ^ (k + 2) - 1) + 2 = 2 ^ (k + 2) + 1 := by omega
    simpa [hidx] using hFib'
  have hEq := Omega.lucasNum_eq_fib (2 ^ (k + 2)) hn
  have hLe : Nat.fib (2 ^ (k + 2) + 1) ≤ Omega.lucasNum (2 ^ (k + 2)) := by
    rw [hEq]
    exact Nat.le_add_right _ _
  exact lt_of_lt_of_le hFib hLe

private theorem fib_two_pow_primeFactors_card_lower :
    ∀ k, k + 1 ≤ (Nat.fib (2 ^ (k + 2))).primeFactors.card
  | 0 => by native_decide
  | k + 1 => by
      let a := Nat.fib (2 ^ (k + 2))
      let b := Nat.fib (2 ^ (k + 3))
      let l := Omega.lucasNum (2 ^ (k + 2))
      have hrec : k + 1 ≤ a.primeFactors.card := by
        simpa [a] using fib_two_pow_primeFactors_card_lower k
      have hb_eq : b = a * l := by
        dsimp [a, b, l]
        simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (Omega.fib_double_eq_mul_lucas (2 ^ (k + 2)))
      have ha_dvd_hb : a ∣ b := ⟨l, hb_eq⟩
      have hl_dvd_hb : l ∣ b := by
        refine ⟨a, ?_⟩
        simpa [Nat.mul_comm] using hb_eq
      have hb_ne_zero : b ≠ 0 := by
        exact Nat.ne_of_gt (Nat.fib_pos.mpr (pow_pos (by decide : 0 < 2) _))
      have hl_gt_one : 1 < l := by
        simpa [l] using lucas_two_pow_gt_one k
      have hl_ne_zero : l ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide) hl_gt_one)
      let p := Nat.minFac l
      have hp : Nat.Prime p := by
        dsimp [p]
        exact Nat.minFac_prime (ne_of_gt hl_gt_one)
      have hp_l : p ∣ l := by
        dsimp [p]
        exact Nat.minFac_dvd l
      have hsubset : a.primeFactors ⊆ b.primeFactors := by
        intro q hq
        have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
        have hq_a : q ∣ a := Nat.dvd_of_mem_primeFactors hq
        exact Nat.mem_primeFactors.mpr ⟨hq_prime, dvd_trans hq_a ha_dvd_hb, hb_ne_zero⟩
      have hgcd : Nat.gcd l a = 1 := by
        dsimp [a, l]
        rw [Omega.lucasNum_fib_gcd_eq (2 ^ (k + 2))]
        simp [three_not_dvd_two_pow (k + 2)]
      have hp_not_mem : p ∉ a.primeFactors := by
        intro hp_mem
        have hp_a : p ∣ a := Nat.dvd_of_mem_primeFactors hp_mem
        have hp_one : p ∣ 1 := by
          simpa [hgcd] using Nat.dvd_gcd hp_l hp_a
        exact hp.ne_one (Nat.dvd_one.mp hp_one)
      have hp_mem_b : p ∈ b.primeFactors := by
        exact Nat.mem_primeFactors.mpr ⟨hp, dvd_trans hp_l hl_dvd_hb, hb_ne_zero⟩
      have hinsert_subset : insert p a.primeFactors ⊆ b.primeFactors := by
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq'
        · exact hp_mem_b
        · exact hsubset hq'
      have hcard_insert : (insert p a.primeFactors).card = a.primeFactors.card + 1 := by
        simp [hp_not_mem]
      calc
        k + 2 ≤ a.primeFactors.card + 1 := by omega
        _ = (insert p a.primeFactors).card := hcard_insert.symm
        _ ≤ b.primeFactors.card := Finset.card_le_card hinsert_subset

/-- The dyadic Fibonacci stages carry unbounded odd prime support, so the `pcdim_∞` surrogate is
already forced to be infinite along `k ↦ fib (2^k)`.
`cor:cdim-fibonacci-2power-adic-unit-infinite` -/
theorem paper_cdim_fibonacci_2power_adic_unit_infinite :
    pcdimInftyFromPrimeGrowth (fun k => Nat.fib (2 ^ k)) id = ⊤ := by
  classical
  have hunbounded : ∀ C, ∃ j, C < (Nat.fib (2 ^ j)).primeFactors.card := by
    intro C
    refine ⟨C + 2, ?_⟩
    have hlower := fib_two_pow_primeFactors_card_lower C
    omega
  simp [pcdimInftyFromPrimeGrowth, hunbounded]

end Omega.CircleDimension
