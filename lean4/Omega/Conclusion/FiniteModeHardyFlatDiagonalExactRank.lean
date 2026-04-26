import Omega.Conclusion.FiniteModeHardyRationalReproducibility

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-finite-mode-hardy-flat-diagonal-exact-rank`. -/
theorem paper_conclusion_finite_mode_hardy_flat_diagonal_exact_rank
    (D : conclusion_finite_mode_hardy_rational_reproducibility_data) (hz : D.z = 1) :
    D.kernel = (D.N : ℚ) ∧ D.rank_eq := by
  refine ⟨?_, ?_⟩
  · simp [conclusion_finite_mode_hardy_rational_reproducibility_data.kernel, hz]
  · simp [conclusion_finite_mode_hardy_rational_reproducibility_data.rank_eq]

end Omega.Conclusion
