import Omega.Zeta.XiPronyDecisionVsReconstructionOneSampleGap

namespace Omega.Zeta

/-- Concrete statement for `cor:xi-prony-decision-reconstruction-one-sample-gap`. -/
def xi_prony_decision_reconstruction_one_sample_gap_statement : Prop :=
  ∀ (decisionSamples reconstructionSamples : Nat) (omega1 omega2 a1 a2 : Int),
    decisionSamples = 3 →
      reconstructionSamples = 4 →
        (hankel2 omega1 omega2 a1 a2 ≠ 0 ↔
            omega1 ≠ 0 ∧ omega2 ≠ 0 ∧ a1 ≠ a2) ∧
          ((pronyJacobian2 a1 a2 omega1 omega2).det ≠ 0 ↔
            omega1 ≠ 0 ∧ omega2 ≠ 0 ∧ a1 ≠ a2)

theorem paper_xi_prony_decision_reconstruction_one_sample_gap :
    xi_prony_decision_reconstruction_one_sample_gap_statement := by
  intro decisionSamples reconstructionSamples omega1 omega2 a1 a2 hDecision hReconstruction
  exact paper_xi_prony_decision_vs_reconstruction_one_sample_gap
    decisionSamples reconstructionSamples omega1 omega2 a1 a2 hDecision hReconstruction

end Omega.Zeta
