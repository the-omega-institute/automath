import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `thm:xi-operator-herglotz-toeplitz-completeness`. -/
theorem paper_xi_operator_herglotz_toeplitz_completeness
    (operatorCaratheodory operatorHerglotz blockToeplitzPSD : Prop)
    (h12 : operatorCaratheodory -> operatorHerglotz)
    (h21 : operatorHerglotz -> operatorCaratheodory)
    (h13 : operatorCaratheodory -> blockToeplitzPSD)
    (h31 : blockToeplitzPSD -> operatorCaratheodory) :
    operatorCaratheodory <-> operatorHerglotz ∧ blockToeplitzPSD := by
  constructor
  · intro hcar
    exact ⟨h12 hcar, h13 hcar⟩
  · intro hpos
    have _ : operatorCaratheodory := h31 hpos.2
    exact h21 hpos.1

end Omega.UnitCirclePhaseArithmetic
