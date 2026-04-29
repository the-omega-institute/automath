import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-rank-two-tate-carpet-finitelevel-kl-additivity`. -/
theorem paper_conclusion_rank_two_tate_carpet_finitelevel_kl_additivity
    (klProduct : ℕ → ℝ) (kl1 kl2 : ℝ) (h0 : klProduct 0 = 0)
    (hstep : ∀ n, klProduct (n + 1) = klProduct n + (kl1 + kl2)) :
    (∀ n, klProduct n = (n : ℝ) * (kl1 + kl2)) ∧
      (0 < kl1 + kl2 → ∀ M : ℝ, ∃ n : ℕ, M ≤ klProduct n) := by
  have hclosed : ∀ n, klProduct n = (n : ℝ) * (kl1 + kl2) := by
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
    obtain ⟨n, hn⟩ := exists_nat_ge (M / (kl1 + kl2))
    refine ⟨n, ?_⟩
    rw [hclosed n]
    have hmul :=
      mul_le_mul_of_nonneg_right hn (le_of_lt hpos)
    simpa [div_mul_cancel₀ M (ne_of_gt hpos)] using hmul

end Omega.Conclusion
