import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-parameterblind-even-parity-splitting`. The reciprocal zeta
factorization follows from `Delta = (1 - v z^2) Q8` and the two reciprocal certificates. -/
theorem paper_conclusion_parameterblind_even_parity_splitting
    (Delta Q8 zeta zetaRed : ℝ → ℝ → ℝ → ℝ)
    (hDelta : ∀ z u v : ℝ, Delta z u v = (1 - v * z ^ 2) * Q8 z u v)
    (hzeta : ∀ z u v : ℝ, zeta z u v * Delta z u v = 1)
    (hzetaRed : ∀ z u v : ℝ, zetaRed z u v * Q8 z u v = 1)
    (hEven : ∀ (z : ℝ) (_u : ℝ) (v : ℝ), 1 - v * z ^ 2 ≠ 0)
    (hQ8 : ∀ z u v : ℝ, Q8 z u v ≠ 0) :
    ∀ z u v : ℝ, zeta z u v = (1 / (1 - v * z ^ 2)) * zetaRed z u v := by
  intro z u v
  have hDelta_ne : Delta z u v ≠ 0 := by
    rw [hDelta z u v]
    exact mul_ne_zero (hEven z u v) (hQ8 z u v)
  have hzeta_eq : zeta z u v = 1 / Delta z u v := by
    field_simp [hDelta_ne]
    exact hzeta z u v
  have hzetaRed_eq : zetaRed z u v = 1 / Q8 z u v := by
    field_simp [hQ8 z u v]
    exact hzetaRed z u v
  calc
    zeta z u v = 1 / Delta z u v := hzeta_eq
    _ = 1 / ((1 - v * z ^ 2) * Q8 z u v) := by rw [hDelta z u v]
    _ = (1 / (1 - v * z ^ 2)) * (1 / Q8 z u v) := by
          field_simp [hEven z u v, hQ8 z u v]
    _ = (1 / (1 - v * z ^ 2)) * zetaRed z u v := by rw [hzetaRed_eq]

end Omega.Conclusion
