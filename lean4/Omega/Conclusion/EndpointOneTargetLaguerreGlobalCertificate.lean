import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-endpoint-one-target-laguerre-global-certificate`. -/
theorem paper_conclusion_endpoint_one_target_laguerre_global_certificate (n : ℕ) (κ : ℝ)
    (p d : ℕ → ℝ) (hn : 0 < n) (hcoeff : ∀ j, j < n → d j = ((j : ℝ) + κ) * p j)
    (hlead : p (n - 1) = (-1 : ℝ) ^ (n - 1)) :
    d (n - 1) = ((((n - 1 : ℕ) : ℝ) + κ) * ((-1 : ℝ) ^ (n - 1))) ∧
      ((-1 : ℝ) ^ (n - 1)) * d (n - 1) - ((n - 1 : ℕ) : ℝ) = κ := by
  have hnsub : n - 1 < n := Nat.sub_lt hn Nat.zero_lt_one
  have hd : d (n - 1) = (((n - 1 : ℕ) : ℝ) + κ) * ((-1 : ℝ) ^ (n - 1)) := by
    simpa [hlead] using hcoeff (n - 1) hnsub
  have hsignsq : ((-1 : ℝ) ^ (n - 1)) * ((-1 : ℝ) ^ (n - 1)) = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  constructor
  · exact hd
  · rw [hd]
    have hmul :
        ((-1 : ℝ) ^ (n - 1)) *
            ((((n - 1 : ℕ) : ℝ) + κ) * ((-1 : ℝ) ^ (n - 1))) =
          (((n - 1 : ℕ) : ℝ) + κ) *
            (((-1 : ℝ) ^ (n - 1)) * ((-1 : ℝ) ^ (n - 1))) := by
      ring
    rw [hmul, hsignsq]
    ring

end Omega.Conclusion
