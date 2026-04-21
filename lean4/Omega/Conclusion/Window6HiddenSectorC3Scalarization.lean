import Mathlib.Tactic

namespace Omega.Conclusion

open Matrix

/-- The `d = 2` hidden-sector perturbation changes the `C₃` weighted moment matrix by a scalar
multiple of the identity. -/
theorem paper_conclusion_window6_hidden_sector_c3_scalarization (f2 f3 f4 eps : ℝ) :
    Matrix.diagonal
        ![4 * (f2 + eps) + 4 * f3 + 8 * f4, 4 * (f2 + eps) + 12 * f4,
          4 * (f2 + eps) + 4 * f3 + 8 * f4] -
      Matrix.diagonal ![4 * f2 + 4 * f3 + 8 * f4, 4 * f2 + 12 * f4, 4 * f2 + 4 * f3 + 8 * f4] =
      (4 * eps) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

end Omega.Conclusion
