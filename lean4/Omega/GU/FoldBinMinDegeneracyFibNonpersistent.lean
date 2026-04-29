import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.GU

private theorem fib_ratio_lower_aux :
    ∀ k : ℕ,
      8 * Nat.fib (k + 5) ≤ 5 * Nat.fib (k + 6) ∧
        8 * Nat.fib (k + 6) ≤ 5 * Nat.fib (k + 7) := by
  intro k
  induction k with
  | zero =>
      norm_num [Nat.fib]
  | succ k ih =>
      rcases ih with ⟨hk, hk'⟩
      refine ⟨hk', ?_⟩
      have h7 : Nat.fib (k + 7) = Nat.fib (k + 5) + Nat.fib (k + 6) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (Nat.fib_add_two (n := k + 5))
      have h8 : Nat.fib (k + 8) = Nat.fib (k + 6) + Nat.fib (k + 7) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (Nat.fib_add_two (n := k + 6))
      calc
        8 * Nat.fib (k + 7) = 8 * Nat.fib (k + 5) + 8 * Nat.fib (k + 6) := by
          rw [h7]
          ring
        _ ≤ 5 * Nat.fib (k + 6) + 5 * Nat.fib (k + 7) := add_le_add hk hk'
        _ = 5 * Nat.fib (k + 8) := by
          rw [h8]
          ring

private theorem fib_ratio_lower (n : ℕ) (hn : 5 ≤ n) :
    8 * Nat.fib n ≤ 5 * Nat.fib (n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (fib_ratio_lower_aux k).1

private theorem fib_product_step (k : ℕ) (hk : 12 ≤ k) :
    4 * (Nat.fib k * Nat.fib (2 * k + 2)) < Nat.fib (k + 1) * Nat.fib (2 * k + 4) := by
  have hkRatio : 8 * Nat.fib k ≤ 5 * Nat.fib (k + 1) := fib_ratio_lower k (by omega)
  have h2kRatio : 8 * Nat.fib (2 * k + 2) ≤ 5 * Nat.fib (2 * k + 3) := by
    apply fib_ratio_lower
    omega
  have h13 : 13 * Nat.fib (2 * k + 2) ≤ 5 * Nat.fib (2 * k + 4) := by
    have hrec := Nat.fib_add_two (n := 2 * k + 2)
    calc
      13 * Nat.fib (2 * k + 2) = 5 * Nat.fib (2 * k + 2) + 8 * Nat.fib (2 * k + 2) := by ring
      _ ≤ 5 * Nat.fib (2 * k + 2) + 5 * Nat.fib (2 * k + 3) := by gcongr
      _ = 5 * Nat.fib (2 * k + 4) := by
        rw [hrec]
        ring
  have h104 :
      104 * (Nat.fib k * Nat.fib (2 * k + 2)) ≤
        25 * (Nat.fib (k + 1) * Nat.fib (2 * k + 4)) := by
    have h1 :
        104 * (Nat.fib k * Nat.fib (2 * k + 2)) ≤
          65 * (Nat.fib (k + 1) * Nat.fib (2 * k + 2)) := by
      calc
        104 * (Nat.fib k * Nat.fib (2 * k + 2))
            = (8 * Nat.fib k) * (13 * Nat.fib (2 * k + 2)) := by ring
        _ ≤ (5 * Nat.fib (k + 1)) * (13 * Nat.fib (2 * k + 2)) :=
          Nat.mul_le_mul_right (13 * Nat.fib (2 * k + 2)) hkRatio
        _ = 65 * (Nat.fib (k + 1) * Nat.fib (2 * k + 2)) := by ring
    have h2 :
        65 * (Nat.fib (k + 1) * Nat.fib (2 * k + 2)) ≤
          25 * (Nat.fib (k + 1) * Nat.fib (2 * k + 4)) := by
      calc
        65 * (Nat.fib (k + 1) * Nat.fib (2 * k + 2))
            = (5 * Nat.fib (k + 1)) * (13 * Nat.fib (2 * k + 2)) := by ring
        _ ≤ (5 * Nat.fib (k + 1)) * (5 * Nat.fib (2 * k + 4)) :=
          Nat.mul_le_mul_left (5 * Nat.fib (k + 1)) h13
        _ = 25 * (Nat.fib (k + 1) * Nat.fib (2 * k + 4)) := by ring
    exact le_trans h1 h2
  have hpos : 0 < Nat.fib k * Nat.fib (2 * k + 2) := by
    exact Nat.mul_pos (Nat.fib_pos.mpr (by omega)) (Nat.fib_pos.mpr (by omega))
  have h25 :
      25 * (4 * (Nat.fib k * Nat.fib (2 * k + 2))) <
        25 * (Nat.fib (k + 1) * Nat.fib (2 * k + 4)) := by
    calc
      25 * (4 * (Nat.fib k * Nat.fib (2 * k + 2)))
          = 100 * (Nat.fib k * Nat.fib (2 * k + 2)) := by ring
      _ < 104 * (Nat.fib k * Nat.fib (2 * k + 2)) := by
          exact Nat.mul_lt_mul_of_pos_right (by decide : 100 < 104) hpos
      _ ≤ 25 * (Nat.fib (k + 1) * Nat.fib (2 * k + 4)) := h104
  exact Nat.lt_of_mul_lt_mul_left h25

private theorem fib_product_dominates_pow_four (k : ℕ) (hk : 12 ≤ k) :
    4 ^ k < Nat.fib k * Nat.fib (2 * k + 2) := by
  induction k, hk using Nat.le_induction with
  | base =>
      native_decide
  | succ k hk ih =>
      have hstep := fib_product_step k hk
      have hpow : 4 ^ (k + 1) = 4 * 4 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hpow]
      exact lt_trans (Nat.mul_lt_mul_of_pos_left ih (by decide)) hstep

private theorem fib_even_product_dominates_pow_two (m : ℕ) (hm_even : Even m) (hm : 24 ≤ m) :
    2 ^ m < Nat.fib (m + 2) * Nat.fib (m / 2) := by
  rcases hm_even with ⟨k, rfl⟩
  have hk : 12 ≤ k := by omega
  have hprod := fib_product_dominates_pow_four k hk
  have hpow : 4 ^ k = 2 ^ (2 * k) := by
    simpa using (Nat.pow_mul 2 2 k).symm
  have hkdiv : (k + k) / 2 = k := by omega
  have hkadd : k + k + 2 = 2 * k + 2 := by omega
  have hk2 : k + k = 2 * k := by omega
  calc
    2 ^ (k + k) = 2 ^ (2 * k) := by rw [hk2]
    _ = 4 ^ k := hpow.symm
    _ < Nat.fib k * Nat.fib (2 * k + 2) := hprod
    _ = Nat.fib (k + k + 2) * Nat.fib ((k + k) / 2) := by rw [Nat.mul_comm, hkadd, hkdiv]

/-- Paper label: `cor:fold-bin-min-degeneracy-fib-nonpersistent`. An infinite tail of even windows
with `d_min(m) = F_{m/2}` contradicts the counting inequality `2^m ≥ |X_m| d_min(m)`. -/
theorem paper_fold_bin_min_degeneracy_fib_nonpersistent (dmin Xcard totalMass : ℕ → ℕ)
    (hXcard : ∀ m, Xcard m = Nat.fib (m + 2))
    (hlower : ∀ m, Xcard m * dmin m ≤ totalMass m) (htotal : ∀ m, totalMass m = 2 ^ m) :
    (∀ N : ℕ, ∃ m ≥ N, Even m ∧ dmin m = Nat.fib (m / 2)) → False := by
  intro hinf
  obtain ⟨m, hm, hmEven, hmDmin⟩ := hinf 24
  have hupper : Xcard m * dmin m ≤ 2 ^ m := by
    calc
      Xcard m * dmin m ≤ totalMass m := hlower m
      _ = 2 ^ m := htotal m
  have hstrict : 2 ^ m < Xcard m * dmin m := by
    rw [hXcard m, hmDmin]
    simpa [Nat.mul_comm] using fib_even_product_dominates_pow_two m hmEven hm
  omega

end Omega.GU
