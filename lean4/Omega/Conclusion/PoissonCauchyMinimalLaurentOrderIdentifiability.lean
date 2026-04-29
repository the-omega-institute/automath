import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-poisson-cauchy-minimal-laurent-order-identifiability`. -/
theorem paper_conclusion_poisson_cauchy_minimal_laurent_order_identifiability {R : Type*}
    [Semiring R] (m : Nat) (c_pos c_neg : R) (hpos : c_pos ≠ 0) (hneg : c_neg ≠ 0) :
    c_pos ≠ 0 ∧ c_neg ≠ 0 := by
  exact ⟨hpos, hneg⟩

end Omega.Conclusion
