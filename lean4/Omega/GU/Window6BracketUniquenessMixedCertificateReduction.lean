import Omega.GU.TerminalGamma6Rigidity
import Omega.GU.Window6IntrinsicBracketFiniteIntegerReduction
import Omega.TypedAddressBiaxialCompletion.CertificateLoop

namespace Omega.GU

/-- Chapter-level wrapper combining the intrinsic-bracket finite reduction, the Toeplitz--PSD
certificate loop, and the terminal `Γ₆` rigidity package.
    thm:window6-bracket-uniqueness-mixed-certificate-reduction -/
theorem paper_window6_bracket_uniqueness_mixed_certificate_reduction
    (D : Omega.GU.Window6IntrinsicBracketFiniteIntegerReductionData)
    (C : Omega.TypedAddressBiaxialCompletion.TypedAddressCertificateLoopData)
    (R : Omega.GU.TerminalGamma6RigidityData) :
    (D.intrinsicBracketExistsUnique ↔ D.finiteIntegerSystemHasUniqueSolution) ∧
      (C.repulsionRadiusTendsToOne ↔ C.toeplitzPsdAll) ∧
      (C.toeplitzPsdAll ↔ C.toeplitzPsdCofinal) ∧
      (R.graphConnected ∧ R.automorphismGroupTrivial) := by
  have hCertificateLoop :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_certificate_loop C
  refine ⟨paper_window6_intrinsic_bracket_finite_integer_reduction D, ?_, ?_,
    paper_terminal_gamma6_rigidity R⟩
  · exact hCertificateLoop.2.2.1
  · exact hCertificateLoop.2.2.2

end Omega.GU
