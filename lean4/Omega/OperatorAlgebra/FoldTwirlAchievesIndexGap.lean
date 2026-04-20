import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldOptimalDelinkingCurve

namespace Omega.OperatorAlgebra

noncomputable section

/-- Paper label: `prop:op-algebra-twirl-achieves-index-gap`. -/
theorem paper_op_algebra_twirl_achieves_index_gap (Gamma : Real) (hGamma : 0 <= Gamma) :
    ∃ randomness : Real,
      randomness = Gamma ∧
        foldSaturatingDelinkingLeakage Gamma randomness = 0 ∧
        foldOptimalDelinkingCurve Gamma randomness = 0 := by
  have hGamma' : 0 ≤ Gamma := hGamma
  have hzero : 0 ≤ Gamma - Gamma := by linarith [hGamma']
  refine ⟨Gamma, rfl, ?_, ?_⟩
  · simp [foldSaturatingDelinkingLeakage]
  · rw [foldOptimalDelinkingCurve, max_eq_left hzero]
    ring

end

end Omega.OperatorAlgebra
