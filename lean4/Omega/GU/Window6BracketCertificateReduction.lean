import Omega.GU.TerminalGamma6Rigidity
import Omega.GU.Window6IntrinsicBracketFiniteIntegerReduction

namespace Omega.GU

/-- Package combining the intrinsic-bracket finite-integer reduction with terminal `Γ₆` rigidity.
    prop:window6-bracket-certificate-reduction -/
theorem paper_window6_bracket_certificate_reduction
    (D : Omega.GU.Window6IntrinsicBracketFiniteIntegerReductionData)
    (R : Omega.GU.TerminalGamma6RigidityData) :
    (D.intrinsicBracketExistsUnique ↔ D.finiteIntegerSystemHasUniqueSolution) ∧
      R.automorphismGroupTrivial := by
  refine ⟨paper_window6_intrinsic_bracket_finite_integer_reduction D, ?_⟩
  exact (paper_terminal_gamma6_rigidity R).2

end Omega.GU
