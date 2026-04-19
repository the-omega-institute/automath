import Omega.GU.Window6BracketUniquenessMixedCertificateReduction
import Omega.GU.Window6IntrinsicBracketModpLiftCriterion

namespace Omega.GU

/-- Chapter-level corollary packaging the finite-integer reduction, the mod-`p` lift criterion,
the mixed-certificate reduction, and the terminal `Γ₆` rigidity audit into one executable
certificate chain for the window-`6` intrinsic bracket theoremization pipeline.
    cor:window6-intrinsic-bracket-theoremization-pipeline -/
theorem paper_window6_intrinsic_bracket_theoremization_pipeline
    (D : Window6IntrinsicBracketFiniteIntegerReductionData)
    (M : Window6IntrinsicBracketModpLiftCriterionData)
    (C : Omega.TypedAddressBiaxialCompletion.TypedAddressCertificateLoopData)
    (R : TerminalGamma6RigidityData) :
    (D.intrinsicBracketExistsUnique ↔ D.finiteIntegerSystemHasUniqueSolution) ∧
      (M.uniqueIntegerSolution ∧ M.characteristicZeroExistenceUniqueness) ∧
      (C.repulsionRadiusTendsToOne ↔ C.toeplitzPsdAll) ∧
      (C.toeplitzPsdAll ↔ C.toeplitzPsdCofinal) ∧
      (R.graphConnected ∧ R.automorphismGroupTrivial) := by
  have hMixed := paper_window6_bracket_uniqueness_mixed_certificate_reduction D C R
  have hModp := paper_window6_intrinsic_bracket_modp_lift_criterion M
  exact ⟨hMixed.1, hModp, hMixed.2.1, hMixed.2.2.1, hMixed.2.2.2⟩

end Omega.GU
