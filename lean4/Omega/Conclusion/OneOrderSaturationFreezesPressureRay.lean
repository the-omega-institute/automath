import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-one-order-saturation-freezes-pressure-ray`. -/
theorem paper_conclusion_one_order_saturation_freezes_pressure_ray
    (P : Nat -> Real) (Lambda I : Real)
    (upper :
      forall q : Nat,
        1 <= q -> P q <= Real.log 2 + (q - 1 : Nat) * Lambda)
    (zero_of_saturation :
      forall q0 : Nat,
        2 <= q0 ->
          P q0 = Real.log 2 + (q0 - 1 : Nat) * Lambda -> I = 0)
    (linear_of_zero :
      I = 0 ->
        forall q : Nat,
          1 <= q -> P q = Real.log 2 + (q - 1 : Nat) * Lambda)
    {q0 : Nat} (hq0 : 2 <= q0)
    (hsat : P q0 = Real.log 2 + (q0 - 1 : Nat) * Lambda) :
    I = 0 /\
      forall q : Nat,
        1 <= q -> P q = Real.log 2 + (q - 1 : Nat) * Lambda := by
  have _ : P q0 <= Real.log 2 + (q0 - 1 : Nat) * Lambda :=
    upper q0 (le_trans (by norm_num : 1 <= 2) hq0)
  have hI : I = 0 := zero_of_saturation q0 hq0 hsat
  exact ⟨hI, linear_of_zero hI⟩

end Omega.Conclusion
