import Mathlib

open scoped BigOperators

namespace Omega.SyncKernelWeighted

private lemma neg_one_pow_sub_eq_neg_neg_one_pow (n k : ℕ) (hn : Odd n) (hk : k ≤ n) :
    (-1 : ℤ) ^ (n - k) = -((-1 : ℤ) ^ k) := by
  have hpow : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n - k) * (-1 : ℤ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have hk_sq : (((-1 : ℤ) ^ k) ^ 2 : ℤ) = 1 := by
    calc
      (((-1 : ℤ) ^ k) ^ 2 : ℤ) = (-1 : ℤ) ^ (k + k) := by rw [pow_two, ← pow_add]
      _ = (-1 : ℤ) ^ (2 * k) := by rw [two_mul]
      _ = 1 := by norm_num
  calc
    (-1 : ℤ) ^ (n - k) = (-1 : ℤ) ^ (n - k) * (((-1 : ℤ) ^ k) ^ 2) := by
      rw [hk_sq, mul_one]
    _ = (((-1 : ℤ) ^ (n - k) * (-1 : ℤ) ^ k) : ℤ) * (-1 : ℤ) ^ k := by ring
    _ = (-1 : ℤ) ^ n * (-1 : ℤ) ^ k := by rw [hpow]
    _ = -((-1 : ℤ) ^ k) := by rw [hn.neg_one_pow]; ring

private lemma traceOddVanish_term_reflect (n k : ℕ) (a : ℕ → ℤ) (hn : Odd n) (hk : k ≤ n)
    (hpal : ∀ j, j ≤ n → a j = a (n - j)) :
    a (n - k) * (-1 : ℤ) ^ (n - k) = -(a k * (-1 : ℤ) ^ k) := by
  rw [hpal k hk, neg_one_pow_sub_eq_neg_neg_one_pow n k hn hk]
  ring

/-- Paper label: `cor:trace-odd-vanish`. -/
theorem paper_trace_odd_vanish (n : ℕ) (a : ℕ → ℤ) (hn : Odd n)
    (hpal : ∀ k, k ≤ n → a k = a (n - k)) :
    Finset.sum (Finset.range (n + 1)) (fun k => a k * (-1 : ℤ) ^ k) = 0 := by
  let term : ℕ → ℤ := fun k => a k * (-1 : ℤ) ^ k
  have hreflect :
      Finset.sum (Finset.range (n + 1)) (fun k => term (n - k)) =
        Finset.sum (Finset.range (n + 1)) term := by
    simpa using (Finset.sum_range_reflect term (n + 1))
  have hterm : ∀ k ∈ Finset.range (n + 1), term (n - k) = -term k := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    dsimp [term]
    exact traceOddVanish_term_reflect n k a hn hk' hpal
  have hsum :
      Finset.sum (Finset.range (n + 1)) term = -Finset.sum (Finset.range (n + 1)) term := by
    calc
      Finset.sum (Finset.range (n + 1)) term =
          Finset.sum (Finset.range (n + 1)) (fun k => term (n - k)) := hreflect.symm
      _ = Finset.sum (Finset.range (n + 1)) (fun k => -term k) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        exact hterm k hk
      _ = -Finset.sum (Finset.range (n + 1)) term := by simp
  have hzero : Finset.sum (Finset.range (n + 1)) term = 0 := by
    omega
  simpa [term] using hzero

end Omega.SyncKernelWeighted
