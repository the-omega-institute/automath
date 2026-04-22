import Mathlib.NumberTheory.Real.Irrational

namespace Omega.POM

/-- Paper label: `thm:pom-renyi-dimension-no-algebraic-irrationality`. -/
theorem paper_pom_renyi_dimension_no_algebraic_irrationality (Dq : Real) (Dq_algebraic : Prop)
    (hNoAlgIrr : Dq_algebraic → Irrational Dq → False) :
    ¬ (Dq_algebraic ∧ Irrational Dq) := by
  intro h
  exact hNoAlgIrr h.1 h.2

end Omega.POM
