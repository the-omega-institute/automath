import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-binary-godel-logistic-finitelevel-kl-linear`. -/
theorem paper_conclusion_binary_godel_logistic_finitelevel_kl_linear
    (kl : ℕ → ℝ) (d : ℝ) (h0 : kl 0 = 0)
    (hstep : ∀ n, kl (n + 1) = kl n + d) :
    (∀ n, kl n = (n : ℝ) * d) ∧
      (0 < d → ∀ M : ℝ, ∃ n : ℕ, M ≤ kl n) := by
  have hclosed : ∀ n, kl n = (n : ℝ) * d := by
    intro n
    induction n with
    | zero =>
        simp [h0]
    | succ n ih =>
        rw [hstep n, ih]
        norm_num
        ring
  constructor
  · exact hclosed
  · intro hpos M
    obtain ⟨n, hn⟩ := exists_nat_ge (M / d)
    refine ⟨n, ?_⟩
    rw [hclosed n]
    have hmul := mul_le_mul_of_nonneg_right hn (le_of_lt hpos)
    simpa [div_mul_cancel₀ M (ne_of_gt hpos)] using hmul

end Omega.Conclusion
