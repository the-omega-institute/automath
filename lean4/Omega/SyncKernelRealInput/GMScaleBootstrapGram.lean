import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete one-scale bootstrap data for the Gram operator. The field
`scalePropagation` is the scale-propagation inequality obtained from the one-scale drop; the
readable predicates below expose the trigger and the propagated polynomial decay statement used
by the paper theorem. -/
structure gm_scale_bootstrap_gram_data where
  baseScale : ℕ
  spectralNorm : ℕ → ℝ
  decayWeight : ℝ → ℕ → ℝ
  eta : ℝ
  scaleConstant : ℝ
  eta_pos : 0 < eta
  oneScaleDrop :
    spectralNorm baseScale ≤ scaleConstant * decayWeight eta baseScale
  scalePropagation :
    ∀ M, baseScale ≤ M → spectralNorm M ≤ scaleConstant * decayWeight (eta / 2) M

namespace gm_scale_bootstrap_gram_data

/-- The concrete trigger: the base Gram operator has the recorded one-scale spectral drop at the
positive bootstrap exponent. -/
def triggeredScaleDrop (D : gm_scale_bootstrap_gram_data) : Prop :=
  D.spectralNorm D.baseScale ≤ D.scaleConstant * D.decayWeight D.eta D.baseScale

/-- Uniform propagated polynomial decay at exponent `eta'` across all scales above the base
scale, expressed through the packaged decay weight. -/
def allScalePolynomialDecay (D : gm_scale_bootstrap_gram_data) (eta' : ℝ) : Prop :=
  ∀ M, D.baseScale ≤ M → D.spectralNorm M ≤ D.scaleConstant * D.decayWeight eta' M

end gm_scale_bootstrap_gram_data

open gm_scale_bootstrap_gram_data

/-- Paper label: `prop:gm-scale-bootstrap-gram`. A one-scale spectral drop together with the
scale-propagation inequality produces the positive propagated exponent `eta / 2`. -/
theorem paper_gm_scale_bootstrap_gram (D : gm_scale_bootstrap_gram_data) :
    D.triggeredScaleDrop → ∃ eta' : Real, 0 < eta' ∧ D.allScalePolynomialDecay eta' := by
  intro _hDrop
  refine ⟨D.eta / 2, ?_, ?_⟩
  · linarith [D.eta_pos]
  · intro M hM
    exact D.scalePropagation M hM

end Omega.SyncKernelRealInput
