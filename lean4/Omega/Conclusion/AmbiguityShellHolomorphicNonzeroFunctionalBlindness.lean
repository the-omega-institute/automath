import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace Omega.Conclusion

open Matrix

/-- Concrete two-dimensional ambiguity-shell block data: a visible spectral value and the
nilpotent upper-right holomorphic-shell coupling. -/
structure conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_data where
  conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_spectralValue : ℂ
  conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_nilpotentCoupling : ℂ

/-- The nilpotent ambiguity-shell block. -/
def conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_nilpotent
    (D : conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_data) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, D.conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_nilpotentCoupling;
    0, 0]

/-- The visible diagonal block seen by spectral trace and determinant functionals. -/
def conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_visible
    (D : conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_data) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![D.conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_spectralValue, 0;
    0, D.conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_spectralValue]

/-- The holomorphic upper-triangular ambiguity-shell block. -/
def conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_block
    (D : conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_data) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_visible D +
    conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_nilpotent D

/-- Trace and determinant functionals are blind to the upper nilpotent shell block. -/
def conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_statement
    (D : conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_data) : Prop :=
  ((conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_block D).trace =
      (conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_visible D).trace) ∧
    ((conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_block D).det =
      (conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_visible D).det) ∧
    ((conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_nilpotent D).trace =
      0) ∧
    ((1 +
        conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_nilpotent D).det =
      1)

/-- Paper label:
`thm:conclusion-ambiguity-shell-holomorphic-nonzero-functional-blindness`. -/
theorem paper_conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness
    (D : conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_data) :
    conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_statement D := by
  simp [conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_statement,
    conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_block,
    conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_visible,
    conclusion_ambiguity_shell_holomorphic_nonzero_functional_blindness_nilpotent,
    Matrix.trace_fin_two, Matrix.det_fin_two]

end Omega.Conclusion
