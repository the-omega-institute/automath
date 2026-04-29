import Mathlib.Tactic

namespace Omega.Conclusion

open Matrix

/-- Paper label: `prop:conclusion-prym-c3-integral-representation`. -/
theorem paper_conclusion_prym_c3_integral_representation :
    (let A : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, -1];
      A ^ 3 = 1 ∧ A ^ 2 + A + 1 = 0) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pow_succ, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two]

end Omega.Conclusion
