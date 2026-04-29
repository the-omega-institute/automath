import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-cauchy-optimal-drift-complete-inversion`. -/
theorem paper_conclusion_poisson_cauchy_optimal_drift_complete_inversion {A B : ℝ}
    {u : Fin 2 → ℝ} {Q : Fin 2 → Fin 2 → ℝ} (hu0 : u 0 = B) (hu1 : u 1 = A)
    (hQ00 : Q 0 0 = u 1 / 2) (hQ01 : Q 0 1 = u 0) (hQ10 : Q 1 0 = u 0)
    (hQ11 : Q 1 1 = -u 1 / 2) :
    u 0 = B ∧ u 1 = A ∧ Q 0 0 = A / 2 ∧ Q 0 1 = B ∧ Q 1 0 = B ∧
      Q 1 1 = -A / 2 := by
  refine ⟨hu0, hu1, ?_, ?_, ?_, ?_⟩
  · rw [hQ00, hu1]
  · rw [hQ01, hu0]
  · rw [hQ10, hu0]
  · rw [hQ11, hu1]

end Omega.Conclusion
