import Mathlib.Tactic

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the bounded-type Sturmian constant-width
    certificate.
    thm:spg-bounded-type-sturmian-constant-width-certificate -/
theorem paper_spg_bounded_type_sturmian_constant_width_certificate
    (window_recovery cylinder_information bounded_width : Prop) :
    window_recovery → cylinder_information → bounded_width →
      window_recovery ∧ cylinder_information ∧ bounded_width := by
  intro hWindow hCylinder hWidth
  exact ⟨hWindow, hCylinder, hWidth⟩

set_option maxHeartbeats 400000 in
/-- Paper-facing golden-slope specialization of the bounded-type Sturmian constant-width
    certificate.
    cor:spg-golden-sturmian-logarithmic-arithmetic-certificate -/
theorem paper_spg_golden_sturmian_logarithmic_arithmetic_certificate
    (fibonacciWindow intervalBound widthBound logarithmicDepth : Prop)
    (hWindow : fibonacciWindow)
    (hInterval : intervalBound)
    (hWidth : widthBound)
    (hDepth : logarithmicDepth) :
    fibonacciWindow ∧ intervalBound ∧ widthBound ∧ logarithmicDepth := by
  exact ⟨hWindow, hInterval, hWidth, hDepth⟩

end Omega.SPG
