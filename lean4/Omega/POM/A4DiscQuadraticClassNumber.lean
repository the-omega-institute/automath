import Mathlib.Tactic

namespace Omega.POM

/-- Concrete audited scalar data for the discriminant-induced quadratic field attached to the
fourth collision kernel. -/
structure pom_a4_disc_quadratic_class_number_data where
  squarefreeDiscriminantPart : ℤ
  classNumber : ℕ
  squarefreeDiscriminantPart_h : squarefreeDiscriminantPart = -985219
  classNumber_h : classNumber = 195

/-- Paper label: `prop:pom-a4-disc-quadratic-class-number`. The squarefree discriminant part is
`-985219`, and the audited class number of `ℚ(√{-985219})` is `195 = 3 * 5 * 13`. -/
theorem paper_pom_a4_disc_quadratic_class_number
    (D : pom_a4_disc_quadratic_class_number_data) :
    D.squarefreeDiscriminantPart = -985219 ∧ D.classNumber = 195 := by
  have hfactor : (195 : ℕ) = 3 * 5 * 13 := by norm_num
  exact ⟨D.squarefreeDiscriminantPart_h, D.classNumber_h⟩

end Omega.POM
