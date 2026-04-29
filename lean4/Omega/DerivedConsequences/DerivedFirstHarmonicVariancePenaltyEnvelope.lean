import Mathlib.Tactic
import Omega.Zeta.XiEntropyGapExponentialSuppressionNonzeroFingerprint

namespace Omega.DerivedConsequences

/-- Derived first-harmonic envelope statement: the Xi-side variance-penalty bound rewrites the
right-hand side as a variance-free envelope minus a nonnegative penalty. -/
def derived_first_harmonic_variance_penalty_envelope_derived_statement {κ : ℕ}
    (mass delta phase : Fin κ → ℝ) : Prop :=
  (∀ j, 0 ≤ mass j) →
    (∀ j, 0 < delta j) →
    (∀ j, |phase j| ≤ 1) →
    0 < Omega.Zeta.xiIndexMass mass →
    let lhs := Real.exp 1 * |Omega.Zeta.xiComovingFourier mass delta phase 1| / (4 * Real.pi)
    let rhs :=
      Omega.Zeta.xiDefectEntropy mass delta *
          (Omega.Zeta.xiIndexMass mass - Omega.Zeta.xiDefectEntropy mass delta) /
        Omega.Zeta.xiIndexMass mass
    let penalty :=
      Omega.Zeta.xiWeightedVariancePenalty mass (Omega.Zeta.xiFirstHarmonicWeight delta)
    lhs ≤ rhs - penalty ∧ lhs ≤ rhs ∧ 0 ≤ penalty ∧ (penalty = 0 → rhs - penalty = rhs)

local notation "derived_first_harmonic_variance_penalty_envelope_statement" =>
  derived_first_harmonic_variance_penalty_envelope_derived_statement

/-- Paper label: `prop:derived-first-harmonic-variance-penalty-envelope`. -/
theorem paper_derived_first_harmonic_variance_penalty_envelope {κ : ℕ}
    (mass delta phase : Fin κ → ℝ) :
    derived_first_harmonic_variance_penalty_envelope_statement mass delta phase := by
  intro hm hδ hphase hmass_pos
  have hmain :=
    Omega.Zeta.paper_xi_first_harmonic_variance_penalty mass delta phase hm hδ hphase hmass_pos
  have hpen_nonneg :
      0 ≤ Omega.Zeta.xiWeightedVariancePenalty mass (Omega.Zeta.xiFirstHarmonicWeight delta) := by
    unfold Omega.Zeta.xiWeightedVariancePenalty
    refine Finset.sum_nonneg ?_
    intro j hj
    exact mul_nonneg (hm j) (sq_nonneg _)
  refine ⟨hmain, ?_, hpen_nonneg, ?_⟩
  · linarith
  · intro hpen_zero
    simp [hpen_zero]

end Omega.DerivedConsequences
