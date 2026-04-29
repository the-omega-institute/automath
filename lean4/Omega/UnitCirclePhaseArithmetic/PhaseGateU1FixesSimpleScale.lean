import Mathlib

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `prop:phase-gate-u1-fixes-simple-scale`. The unique admissible scale factor is
the ratio `sqtarget / sqnorm0`, and positivity follows from the positivity of both squared norms.
-/
theorem paper_phase_gate_u1_fixes_simple_scale (sqnorm0 sqtarget : ℝ) (hsqnorm0 : 0 < sqnorm0)
    (hsqtarget : 0 < sqtarget) : ∃! c : ℝ, 0 < c ∧ c * sqnorm0 = sqtarget := by
  have hsqnorm0_ne : sqnorm0 ≠ 0 := ne_of_gt hsqnorm0
  refine ⟨sqtarget / sqnorm0, ?_, ?_⟩
  · constructor
    · exact div_pos hsqtarget hsqnorm0
    · field_simp [hsqnorm0_ne]
  · intro c hc
    exact (eq_div_iff hsqnorm0_ne).2 hc.2

end Omega.UnitCirclePhaseArithmetic
