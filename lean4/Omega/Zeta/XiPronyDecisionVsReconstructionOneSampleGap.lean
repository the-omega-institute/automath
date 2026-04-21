import Mathlib.Tactic
import Omega.Zeta.HankelVandermonde3Recovery
import Omega.Zeta.XiPronyMomentMapJacobianDelta4

namespace Omega.Zeta

/-- In the `κ = 2` Prony model, three samples suffice to decide general position via the Hankel
determinant, while four samples give local reconstruction via the Jacobian; both thresholds are
cut out by the same nondegeneracy conditions.
    cor:xi-prony-decision-vs-reconstruction-one-sample-gap -/
theorem paper_xi_prony_decision_vs_reconstruction_one_sample_gap
    (decisionSamples reconstructionSamples : Nat) (omega1 omega2 a1 a2 : Int)
    (hDecisionSamples : decisionSamples = 3) (hReconstructionSamples : reconstructionSamples = 4) :
    (hankel2 omega1 omega2 a1 a2 ≠ 0 ↔ omega1 ≠ 0 ∧ omega2 ≠ 0 ∧ a1 ≠ a2) ∧
      ((pronyJacobian2 a1 a2 omega1 omega2).det ≠ 0 ↔
        omega1 ≠ 0 ∧ omega2 ≠ 0 ∧ a1 ≠ a2) := by
  cases hDecisionSamples
  cases hReconstructionSamples
  refine ⟨hankel2_ne_zero_iff omega1 omega2 a1 a2, ?_⟩
  rw [paper_xi_prony_moment_map_jacobian_delta4]
  rw [show -omega1 * omega2 * (a2 - a1) ^ 4 = (-omega1) * (omega2 * (a2 - a1) ^ 4) by ring]
  rw [mul_ne_zero_iff, mul_ne_zero_iff, pow_ne_zero_iff (by norm_num : (4 : ℕ) ≠ 0), sub_ne_zero]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨neg_ne_zero.mp h1, h2, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨neg_ne_zero.mpr h1, h2, h3.symm⟩

end Omega.Zeta
