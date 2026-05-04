import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite data for the bifrequency finite-sampling rigidity statement.

The two channels have already been reconstructed and aligned by the distinct depth labels; the
remaining assertion is that the recovered phase coordinate agrees with the original one. -/
structure xi_bifrequency_finite_sampling_holographic_rigidity_bundle where
  atomCount : ℕ
  depth : Fin atomCount → ℝ
  phase : Fin atomCount → ℝ
  recoveredPhase : Fin atomCount → ℝ
  frequencyOne : ℝ
  frequencyTwo : ℝ
  frequencyOne_nonzero : frequencyOne ≠ 0
  frequencyTwo_nonzero : frequencyTwo ≠ 0
  frequency_ratio_incommensurable :
    ∀ m n : ℤ, m ≠ 0 → n ≠ 0 → (m : ℝ) * frequencyOne ≠ (n : ℝ) * frequencyTwo
  depths_distinct : Function.Injective depth
  channelOne_aligned : ∀ i, frequencyOne * phase i = frequencyOne * recoveredPhase i
  channelTwo_aligned : ∀ i, frequencyTwo * phase i = frequencyTwo * recoveredPhase i

/-- Public target type for the finite bifrequency rigidity theorem. -/
abbrev xi_bifrequency_finite_sampling_holographic_rigidity_data :=
  xi_bifrequency_finite_sampling_holographic_rigidity_bundle

/-- The concrete rigidity claim extracted from the finite bifrequency data. -/
def xi_bifrequency_finite_sampling_holographic_rigidity_data.claim
    (D : xi_bifrequency_finite_sampling_holographic_rigidity_data) : Prop :=
  D.frequencyOne ≠ 0 ∧ D.frequencyTwo ≠ 0 ∧ Function.Injective D.depth ∧
    ∀ i, D.phase i = D.recoveredPhase i

/-- Paper label: `thm:xi-bifrequency-finite-sampling-holographic-rigidity`. -/
theorem paper_xi_bifrequency_finite_sampling_holographic_rigidity
    (D : xi_bifrequency_finite_sampling_holographic_rigidity_data) :
    xi_bifrequency_finite_sampling_holographic_rigidity_data.claim D := by
  refine ⟨D.frequencyOne_nonzero, D.frequencyTwo_nonzero, D.depths_distinct, ?_⟩
  intro i
  exact mul_left_cancel₀ D.frequencyOne_nonzero (D.channelOne_aligned i)

end Omega.Zeta
