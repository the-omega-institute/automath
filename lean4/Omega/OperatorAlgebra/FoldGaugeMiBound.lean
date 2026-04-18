import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Concrete visible-fiber data for the fold-gauge mutual-information bound. The learner law is a
scalar proxy for the conditional law on the hidden state, `visibleSection` picks a representative
from each visible fiber, and the numeric fields record the data-processing comparison together
with the entropy identity `H(X^n) = n * H(π)`. -/
structure FoldGaugeMiBoundData where
  visibleStates : ℕ
  hiddenStates : ℕ
  visible : Fin hiddenStates → Fin visibleStates
  visibleSection : Fin visibleStates → Fin hiddenStates
  visible_section : ∀ v, visible (visibleSection v) = v
  learnerLaw : Fin hiddenStates → ℚ
  sampleCount : ℕ
  baseEntropy : ℚ
  learnerMutualInfo : ℚ
  visibleMutualInfo : ℚ
  fiberwiseTransitive :
    ∀ x y, visible x = visible y → learnerLaw x = learnerLaw y
  dataProcessing_h : learnerMutualInfo ≤ visibleMutualInfo
  visibleEntropy_h : visibleMutualInfo = (sampleCount : ℚ) * baseEntropy

/-- The induced visible random map obtained by evaluating the learner law on the chosen visible
fiber representative. -/
def inducedVisibleLaw (D : FoldGaugeMiBoundData) (v : Fin D.visibleStates) : ℚ :=
  D.learnerLaw (D.visibleSection v)

/-- The learner law factors through the visible variables when it is constant on every visible
fiber. -/
def FoldGaugeMiBoundData.factorsThroughVisibleVariables (D : FoldGaugeMiBoundData) : Prop :=
  ∀ x, D.learnerLaw x = inducedVisibleLaw D (D.visible x)

/-- Scalar proxy for the entropy identity `H(X^n) = n * H(π)`. -/
def foldGaugeSampleEntropy (n : ℕ) (piEntropy : ℚ) : ℚ :=
  (n : ℚ) * piEntropy

/-- Mutual information is bounded by the visible entropy and hence by `n * H(π)`. -/
def FoldGaugeMiBoundData.informationComplexityBound (D : FoldGaugeMiBoundData) : Prop :=
  D.learnerMutualInfo ≤ foldGaugeSampleEntropy D.sampleCount D.baseEntropy

/-- Paper label: `prop:op-algebra-fold-gauge-mi-bound`.
Fiberwise transitivity makes the learner law constant on visible fibers, so it factors through
the visible variables; data processing and `H(X^n) = n * H(π)` then yield the information bound.
-/
theorem paper_op_algebra_fold_gauge_mi_bound (D : FoldGaugeMiBoundData) :
    D.factorsThroughVisibleVariables ∧ D.informationComplexityBound := by
  constructor
  · intro x
    unfold inducedVisibleLaw
    exact D.fiberwiseTransitive x (D.visibleSection (D.visible x)) (D.visible_section _).symm
  · dsimp [FoldGaugeMiBoundData.informationComplexityBound, foldGaugeSampleEntropy]
    calc
      D.learnerMutualInfo ≤ D.visibleMutualInfo := D.dataProcessing_h
      _ = (D.sampleCount : ℚ) * D.baseEntropy := D.visibleEntropy_h

end Omega.OperatorAlgebra
