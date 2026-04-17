import Omega.Folding.FiberWeightCountComplement
import Omega.Folding.MomentBounds
import Mathlib.Algebra.BigOperators.Intervals

namespace Omega

open scoped BigOperators

private theorem neg_one_pow_square (r : ℕ) : ((-1 : ℤ) ^ r) * ((-1 : ℤ) ^ r) = 1 := by
  calc
    ((-1 : ℤ) ^ r) * ((-1 : ℤ) ^ r) = (-1 : ℤ) ^ (r + r) := by rw [← pow_add]
    _ = (-1 : ℤ) ^ (2 * r) := by congr; omega
    _ = 1 := by simp [Even.neg_one_pow (even_two_mul r)]

private theorem neg_one_pow_even_sub (n r : ℕ) (hn : Even n) (hr : r ≤ n) :
    (-1 : ℤ) ^ (n - r) = (-1 : ℤ) ^ r := by
  have hsq := neg_one_pow_square r
  have hprod : ((-1 : ℤ) ^ r) * ((-1 : ℤ) ^ (n - r)) = 1 := by
    calc
      ((-1 : ℤ) ^ r) * ((-1 : ℤ) ^ (n - r)) = (-1 : ℤ) ^ (r + (n - r)) := by
        rw [← pow_add]
      _ = (-1 : ℤ) ^ n := by congr; omega
      _ = 1 := Even.neg_one_pow hn
  calc
    (-1 : ℤ) ^ (n - r) = (((-1 : ℤ) ^ r) * ((-1 : ℤ) ^ r)) * ((-1 : ℤ) ^ (n - r)) := by
      rw [hsq, one_mul]
    _ = ((-1 : ℤ) ^ r) * (((-1 : ℤ) ^ r) * ((-1 : ℤ) ^ (n - r))) := by ac_rfl
    _ = ((-1 : ℤ) ^ r) * 1 := by rw [hprod]
    _ = (-1 : ℤ) ^ r := by simp

/-- Complement reflection annihilates the second character when `F_{m+2}` is even.
    prop:fold-second-character-reflection-annihilation -/
theorem paper_fold_second_character_reflection_annihilation (m q : ℕ) (hm : 2 ≤ m) (hq : 1 ≤ q)
    (hEven : Even (Nat.fib (m + 2))) :
    (Finset.range (Nat.fib (m + 2))).sum
      (fun r => ((-1 : ℤ) ^ r) * (weightCongruenceCount m r : ℤ) ^ q) = 0 := by
  let N := Nat.fib (m + 2)
  let a := Nat.fib (m + 1) - 2
  let natTerm : ℕ → ℤ := fun r => ((-1 : ℤ) ^ r) * (weightCongruenceCount m r : ℤ) ^ q
  let _ := hq
  have hNpos : 0 < N := by
    dsimp [N]
    exact fib_succ_pos (m + 1)
  have ha_lt : a < N := by
    dsimp [a, N]
    have hfib : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
    omega
  have htop : Nat.fib (m + 3) - 2 = N + a := by
    dsimp [N, a]
    rw [Nat.fib_add_two]
    have hF1_ge2 : 2 ≤ Nat.fib (m + 1) := by
      calc
        Nat.fib (m + 1) ≥ Nat.fib 3 := Nat.fib_mono (by omega)
        _ = 2 := by native_decide
    have hcomm : Nat.fib (m + 1) + Nat.fib (m + 2) - 2 =
        Nat.fib (m + 2) + Nat.fib (m + 1) - 2 := by ac_rfl
    rw [hcomm, Nat.add_sub_assoc hF1_ge2]
  let σ : Fin N → Fin N := fun r =>
    if hr : r.1 ≤ a then ⟨a - r.1, by omega⟩ else ⟨N + a - r.1, by omega⟩
  have hσ : Function.Involutive σ := by
    intro r
    by_cases hr : r.1 ≤ a
    · ext
      simp [σ, hr]
      omega
    · have hbranch : ¬ N + a ≤ a + r.1 := by
        omega
      ext
      simp [σ, hr, hbranch]
      omega
  let term : Fin N → ℤ := fun r => natTerm r.1
  have hterm : ∀ r, term (σ r) = ((-1 : ℤ) ^ a) * term r := by
    intro r
    by_cases hr : r.1 ≤ a
    · have hcount : weightCongruenceCount m (σ r).1 = weightCongruenceCount m r.1 := by
        simpa [σ, hr] using weightCongruenceCount_complement m hm r.1 r.2 hr
      have hprod : ((-1 : ℤ) ^ r.1) * ((-1 : ℤ) ^ (σ r).1) = (-1 : ℤ) ^ a := by
        calc
          ((-1 : ℤ) ^ r.1) * ((-1 : ℤ) ^ (σ r).1) =
              ((-1 : ℤ) ^ r.1) * ((-1 : ℤ) ^ (a - r.1)) := by simp [σ, hr]
          _ = (-1 : ℤ) ^ (r.1 + (a - r.1)) := by rw [← pow_add]
          _ = (-1 : ℤ) ^ a := by congr; omega
      have hsign : (-1 : ℤ) ^ (σ r).1 = ((-1 : ℤ) ^ a) * ((-1 : ℤ) ^ r.1) := by
        calc
          (-1 : ℤ) ^ (σ r).1 =
              (((-1 : ℤ) ^ r.1) * ((-1 : ℤ) ^ r.1)) * ((-1 : ℤ) ^ (σ r).1) := by
                rw [neg_one_pow_square, one_mul]
          _ = ((-1 : ℤ) ^ r.1) * (((-1 : ℤ) ^ r.1) * ((-1 : ℤ) ^ (σ r).1)) := by ac_rfl
          _ = ((-1 : ℤ) ^ r.1) * ((-1 : ℤ) ^ a) := by rw [hprod]
          _ = ((-1 : ℤ) ^ a) * ((-1 : ℤ) ^ r.1) := by ac_rfl
      simp [term, natTerm, hsign, hcount, mul_assoc, mul_left_comm, mul_comm]
    · have hs_val : (σ r).1 = N + a - r.1 := by
        simp [σ, hr]
      have hcount : weightCongruenceCount m (σ r).1 = weightCongruenceCount m r.1 := by
        rw [weightCongruenceCount_eq_sum_ewc m (σ r).1 (by rw [hs_val]; omega),
          weightCongruenceCount_eq_sum_ewc m r.1 r.2]
        have hsym : exactWeightCount m (σ r).1 = exactWeightCount m r.1 := by
          rw [hs_val, exactWeightCount_symmetric m (N + a - r.1) (by rw [← htop]; omega)]
          rw [htop]
          congr
          omega
        have hzero1 : exactWeightCount m ((σ r).1 + N) = 0 := by
          apply Nat.eq_zero_of_not_pos
          rw [exactWeightCount_pos_iff, hs_val, htop]
          omega
        have hzero2 : exactWeightCount m (r.1 + N) = 0 := by
          apply Nat.eq_zero_of_not_pos
          rw [exactWeightCount_pos_iff, htop]
          omega
        rw [hzero1, hzero2, hsym]
      have hsign : (-1 : ℤ) ^ (σ r).1 = ((-1 : ℤ) ^ a) * ((-1 : ℤ) ^ r.1) := by
        calc
          (-1 : ℤ) ^ (σ r).1 = (-1 : ℤ) ^ (a + (N - r.1)) := by
            rw [hs_val]
            congr
            omega
          _ = ((-1 : ℤ) ^ a) * ((-1 : ℤ) ^ (N - r.1)) := by rw [pow_add]
          _ = ((-1 : ℤ) ^ a) * ((-1 : ℤ) ^ r.1) := by
            rw [neg_one_pow_even_sub N r.1 (by simpa [N] using hEven) (le_of_lt r.2)]
      simp [term, natTerm, hsign, hcount, mul_assoc, mul_left_comm, mul_comm]
  have hsum_perm : (∑ r : Fin N, term (σ r)) = ∑ r : Fin N, term r := by
    exact (Function.Involutive.bijective hσ).sum_comp term
  have hsum_scale : (∑ r : Fin N, term (σ r)) = ((-1 : ℤ) ^ a) * ∑ r : Fin N, term r := by
    simp_rw [hterm]
    simpa using (Finset.mul_sum Finset.univ (fun r : Fin N => term r) ((-1 : ℤ) ^ a)).symm
  have hsum_eq : (∑ r : Fin N, term r) = ((-1 : ℤ) ^ a) * ∑ r : Fin N, term r := by
    calc
      (∑ r : Fin N, term r) = ∑ r : Fin N, term (σ r) := hsum_perm.symm
      _ = ((-1 : ℤ) ^ a) * ∑ r : Fin N, term r := hsum_scale
  have hFibOdd : Odd (Nat.fib (m + 1)) := by
    apply Nat.not_even_iff_odd.mp
    intro hEvenPrev
    have hmod_cur : Nat.fib (m + 2) % 2 = 0 := by simpa [Nat.even_iff] using hEven
    have hmod_prev : Nat.fib (m + 1) % 2 = 0 := by simpa [Nat.even_iff] using hEvenPrev
    have h2_cur : 2 ∣ Nat.fib (m + 2) := Nat.dvd_of_mod_eq_zero hmod_cur
    have h2_prev : 2 ∣ Nat.fib (m + 1) := Nat.dvd_of_mod_eq_zero hmod_prev
    have h3_cur : 3 ∣ m + 2 := (fib_even_iff_three_dvd (m + 2)).mp h2_cur
    have h3_prev : 3 ∣ m + 1 := (fib_even_iff_three_dvd (m + 1)).mp h2_prev
    omega
  have hoddA : Odd a := by
    dsimp [a]
    rcases hFibOdd with ⟨k, hk⟩
    have hF1_ge2 : 2 ≤ Nat.fib (m + 1) := by
      calc
        Nat.fib (m + 1) ≥ Nat.fib 3 := Nat.fib_mono (by omega)
        _ = 2 := by native_decide
    have hk_ge1 : 1 ≤ k := by omega
    refine ⟨k - 1, ?_⟩
    omega
  have hsignA : ((-1 : ℤ) ^ a) = -1 := Odd.neg_one_pow hoddA
  have hFin : (∑ r : Fin N, term r) = 0 := by
    rw [hsignA, neg_mul] at hsum_eq
    linarith
  rw [Fin.sum_univ_eq_sum_range natTerm] at hFin
  simpa [term, natTerm, N] using hFin

end Omega
