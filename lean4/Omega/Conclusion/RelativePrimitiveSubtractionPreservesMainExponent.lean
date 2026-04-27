import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-relative-primitive-subtraction-preserves-main-exponent`. -/
theorem paper_conclusion_relative_primitive_subtraction_preserves_main_exponent
    (SharesMainExponent : (Nat -> Real) -> (Nat -> Real) -> Prop) (pB pM q : Nat -> Real)
    (h_q : q = fun n => pB n - pM n) (h_main : SharesMainExponent q pB) :
    SharesMainExponent q pB := by
  simpa [h_q] using h_main

end Omega.Conclusion
