import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.SyncKernelWeighted.RealInput40LengthMertens
import Omega.SyncKernelWeighted.RealInput40LengthSignL1

namespace Omega.Conclusion

open scoped goldenRatio

/-- Concrete statement for the length-parity Mertens split and the algebraic torsion Euler value. -/
def conclusion_length_parity_algebraic_euler_torsion_statement : Prop :=
  Omega.SyncKernelWeighted.realInput40LengthConstant 2 0 =
      Omega.SyncKernelWeighted.realInput40LengthMainTerm 2 +
        ∑' j : ℕ, Omega.SyncKernelWeighted.realInput40LengthTwist 2 0 (j + 1) ∧
    Omega.SyncKernelWeighted.realInput40LengthConstant 2 1 =
      Omega.SyncKernelWeighted.realInput40LengthMainTerm 2 +
        ∑' j : ℕ, Omega.SyncKernelWeighted.realInput40LengthTwist 2 1 (j + 1) ∧
    (let lam : ℝ := (3 + Real.sqrt 5) / 2
     let z : ℝ := -1 / lam
     (((1 - z) ^ 2 * (1 + z) ^ 3 * (1 - 3 * z + z ^ 2) * (1 + z - z ^ 2)) : ℝ)⁻¹ =
        (41 : ℝ) / 40 + (11 : ℝ) / 24 * Real.sqrt 5)

/-- Paper label: `cor:conclusion-length-parity-algebraic-euler-torsion`. -/
theorem paper_conclusion_length_parity_algebraic_euler_torsion :
    conclusion_length_parity_algebraic_euler_torsion_statement := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Omega.SyncKernelWeighted.paper_real_input_40_length_mertens_prog 2 0).2.2
  · exact (Omega.SyncKernelWeighted.paper_real_input_40_length_mertens_prog 2 1).2.2
  · exact Omega.SyncKernelWeighted.paper_real_input_40_length_sign_l1

end Omega.Conclusion
