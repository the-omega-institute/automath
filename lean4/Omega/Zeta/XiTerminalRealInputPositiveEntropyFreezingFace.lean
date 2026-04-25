import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40AlphaMax
import Omega.SyncKernelWeighted.RealInput40PositiveEntropyFreezing

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-real-input-positive-entropy-freezing-face`. -/
theorem paper_xi_terminal_real_input_positive_entropy_freezing_face (c y : Real) (hc : 1 < c)
    (hy : y ^ 4 - 6 * y ^ 3 + 9 * y ^ 2 - y - 1 = 0) (hcy : c = Real.sqrt y) :
    y ^ 4 - 6 * y ^ 3 + 9 * y ^ 2 - y - 1 = 0 ∧
      c = Real.sqrt y ∧
      Omega.SyncKernelWeighted.real_input_40_alpha_max_value = (1 / 2 : Real) ∧
      Omega.SyncKernelWeighted.realInput40GroundEntropy c = Real.log c ∧
      Real.log (Real.goldenRatio ^ 2 / c) =
        Real.log (Real.goldenRatio ^ 2) - Omega.SyncKernelWeighted.realInput40GroundEntropy c := by
  have hAlpha := Omega.SyncKernelWeighted.paper_real_input_40_alpha_max
  have hFreeze := Omega.SyncKernelWeighted.paper_killo_real_input_40_positive_entropy_freezing c hc
  exact ⟨hy, hcy, hAlpha.2.2.2.2, hFreeze.2.1, hFreeze.2.2⟩

end Omega.Zeta
