import Mathlib

open scoped BigOperators

namespace Omega.SyncKernelWeighted

private lemma traceCentralMoment_term_reflect
    (n m k : ℕ) (a : ℕ → ℚ) (hk : k ≤ n) (hpal : ∀ j, j ≤ n → a j = a (n - j)) :
    ((((n - k : ℕ) : ℚ) - (n : ℚ) / 2) ^ (2 * m + 1)) * a (n - k) =
      -(((((k : ℚ) - (n : ℚ) / 2) ^ (2 * m + 1)) * a k) : ℚ) := by
  have hkq : ((n - k : ℕ) : ℚ) + (k : ℚ) = (n : ℚ) := by
    exact_mod_cast (Nat.sub_add_cancel hk)
  have hcenter : (((n - k : ℕ) : ℚ) - (n : ℚ) / 2) = (n : ℚ) / 2 - k := by
    linarith
  have hflip : (n : ℚ) / 2 - k = -((k : ℚ) - (n : ℚ) / 2) := by
    ring
  have hodd : Odd (2 * m + 1) := by
    exact ⟨m, by ring⟩
  rw [hpal k hk, hcenter, hflip, hodd.neg_pow]
  ring

/-- Paper label: `cor:trace-central-moments-zero` -/
theorem paper_trace_central_moments_zero (n m : ℕ) (a : ℕ → ℚ)
    (hpal : ∀ k, k ≤ n → a k = a (n - k)) :
    Finset.sum (Finset.range (n + 1))
      (fun k => (((k : ℚ) - (n : ℚ) / 2) ^ (2 * m + 1)) * a k) = 0 := by
  let term : ℕ → ℚ := fun k => (((k : ℚ) - (n : ℚ) / 2) ^ (2 * m + 1)) * a k
  have hreflect :
      Finset.sum (Finset.range (n + 1)) (fun k => term (n - k)) =
        Finset.sum (Finset.range (n + 1)) term := by
    simpa using (Finset.sum_range_reflect term (n + 1))
  have hterm : ∀ k ∈ Finset.range (n + 1), term (n - k) = -term k := by
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    dsimp [term]
    exact traceCentralMoment_term_reflect n m k a hk_le hpal
  have hsum :
      Finset.sum (Finset.range (n + 1)) term = -Finset.sum (Finset.range (n + 1)) term := by
    calc
      Finset.sum (Finset.range (n + 1)) term =
          Finset.sum (Finset.range (n + 1)) (fun k => term (n - k)) :=
        hreflect.symm
      _ = Finset.sum (Finset.range (n + 1)) (fun k => -term k) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        exact hterm k hk
      _ = -Finset.sum (Finset.range (n + 1)) term := by
        simp
  have hzero : Finset.sum (Finset.range (n + 1)) term = 0 := by
    linarith
  simpa [term] using hzero

end Omega.SyncKernelWeighted
