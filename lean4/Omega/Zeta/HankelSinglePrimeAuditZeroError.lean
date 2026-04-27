import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

namespace Omega.Zeta

open Finset

/-- Paper label: `prop:xi-hankel-single-prime-audit-zero-error`.
An integer Hankel-audit vector that vanishes modulo one prime larger than the coordinate
bound already vanishes over the integers; Bertrand supplies a prime below `2M`. -/
theorem paper_xi_hankel_single_prime_audit_zero_error {n B M p : ℕ}
    (H : Fin n → Fin n → ℤ) (s : Fin n → ℤ)
    (hB : ∀ i j, Int.natAbs (H i j) ≤ B)
    (hM : M = n ^ 2 * B * ((Finset.univ : Finset (Fin n)).sup fun i => Int.natAbs (s i)))
    (hp : Nat.Prime p) (hpM : M < p) :
    ((∀ i, ((∑ j : Fin n, H i j * s j : ℤ) : ZMod p) = 0) ↔
        ∀ i, ∑ j : Fin n, H i j * s j = 0) ∧
      (2 ≤ M → ∃ q : ℕ, Nat.Prime q ∧ M < q ∧ q < 2 * M) := by
  have _hp_ne_one : p ≠ 1 := hp.ne_one
  constructor
  · constructor
    · intro hmod i
      let vmax := (Finset.univ : Finset (Fin n)).sup fun j => Int.natAbs (s j)
      have hs_le : ∀ j : Fin n, Int.natAbs (s j) ≤ vmax := by
        intro j
        exact Finset.le_sup (f := fun j : Fin n => Int.natAbs (s j)) (Finset.mem_univ j)
      have hterm : ∀ j : Fin n, Int.natAbs (H i j * s j) ≤ B * vmax := by
        intro j
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (hB i j) (hs_le j)
      have hsum_terms :
          (∑ j : Fin n, Int.natAbs (H i j * s j)) ≤ n * (B * vmax) := by
        calc
          (∑ j : Fin n, Int.natAbs (H i j * s j))
              ≤ ∑ _j : Fin n, B * vmax := by
                exact Finset.sum_le_sum fun j _ => hterm j
          _ = n * (B * vmax) := by simp
      have hsum_abs :
          Int.natAbs (∑ j : Fin n, H i j * s j) ≤
            ∑ j : Fin n, Int.natAbs (H i j * s j) := by
        have hset : ∀ t : Finset (Fin n),
            Int.natAbs (∑ j ∈ t, H i j * s j) ≤
              ∑ j ∈ t, Int.natAbs (H i j * s j) := by
          intro t
          refine Finset.induction_on t ?base ?step
          · simp
          · intro a t hat ih
            rw [Finset.sum_insert hat, Finset.sum_insert hat]
            exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)
        simpa using hset Finset.univ
      have hn_le_sq : n ≤ n ^ 2 := by
        have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.1) i.2
        nlinarith [Nat.mul_le_mul_left n (Nat.succ_le_of_lt hnpos)]
      have hcoord :
          Int.natAbs (∑ j : Fin n, H i j * s j) ≤ M := by
        have hsmall :
            Int.natAbs (∑ j : Fin n, H i j * s j) ≤ n * (B * vmax) :=
          hsum_abs.trans hsum_terms
        have hlarge : n * (B * vmax) ≤ n ^ 2 * B * vmax := by
          calc
            n * (B * vmax) ≤ n ^ 2 * (B * vmax) := by
              exact Nat.mul_le_mul_right (B * vmax) hn_le_sq
            _ = n ^ 2 * B * vmax := by ring
        have hvmax :
            vmax = (Finset.univ : Finset (Fin n)).sup fun j => Int.natAbs (s j) := rfl
        calc
          Int.natAbs (∑ j : Fin n, H i j * s j) ≤ n * (B * vmax) := hsmall
          _ ≤ n ^ 2 * B * vmax := hlarge
          _ = M := by rw [hM, hvmax]
      have hdiv : (p : ℤ) ∣ (∑ j : Fin n, H i j * s j : ℤ) := by
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (∑ j : Fin n, H i j * s j) p).mp
          (hmod i)
      exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv (by
        simpa using lt_of_le_of_lt hcoord hpM)
    · intro hzero i
      rw [hzero i]
      norm_num
  · intro hM2
    rcases Nat.exists_prime_lt_and_le_two_mul M (by omega) with ⟨q, hqprime, hMq, hqle⟩
    have hqne : q ≠ 2 * M := by
      intro hqeq
      have hqge4 : 4 ≤ q := by omega
      rcases hqprime.eq_two_or_odd' with hq_two | hq_odd
      · omega
      · rcases hq_odd with ⟨k, hk⟩
        omega
    exact ⟨q, hqprime, hMq, lt_of_le_of_ne hqle hqne⟩

end Omega.Zeta
