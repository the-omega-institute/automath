import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-golden-lucas-hankel-v5-quadratic-growth`. If the valuation
has quadratic main term plus an `O(q log q)` error term, then subtracting the main term inherits
the same error bound. -/
theorem paper_conclusion_golden_lucas_hankel_v5_quadratic_growth (v5D err : ℕ → ℝ)
    (herr : ∃ C N, ∀ q, N ≤ q → |err q| ≤ C * q * Real.log (q + 1))
    (hmain : ∀ q, v5D q = (3 / 4 : ℝ) * q^2 + err q) :
    ∃ C N, ∀ q, N ≤ q →
      |v5D q - (3 / 4 : ℝ) * q^2| ≤ C * q * Real.log (q + 1) := by
  rcases herr with ⟨C, N, hC⟩
  refine ⟨C, N, ?_⟩
  intro q hq
  rw [hmain q]
  ring_nf
  simpa [mul_assoc, mul_comm, mul_left_comm, add_comm] using hC q hq

end Omega.Conclusion
