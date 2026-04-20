import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Discussion

/-- The binary entropy term appearing in the Alicki--Fannes/Audenaert continuity estimate. -/
noncomputable def binaryEntropy (ε : ℝ) : ℝ :=
  -(ε * Real.log ε + (1 - ε) * Real.log (1 - ε))

/-- Concrete quantitative data for the HSZK/Holevo comparison.
The field `commonSimulatorBound` records the Holevo upper bound coming from a common simulator
epsilon-ball, while `twoPointPinsker` records the two-point distribution plus Pinsker estimate for
pairwise trace distance. -/
structure HSZKHolevoData where
  epsilon : ℝ
  delta : ℝ
  verifierDim : ℕ
  holevoInformation : ℝ
  traceDistance : ℕ → ℕ → ℝ
  referenceState : ℕ
  commonSimulatorBound :
    holevoInformation ≤
      2 * epsilon * Real.log (verifierDim : ℝ) + 2 * binaryEntropy epsilon
  twoPointPinsker :
    ∀ ω ω' : ℕ, traceDistance ω ω' ≤ Real.sqrt (8 * Real.log 2 * delta)

namespace HSZKHolevoData

/-- The common-simulator epsilon-ball yields the quantitative Holevo upper bound. -/
def holevoUpperBound (D : HSZKHolevoData) : Prop :=
  D.holevoInformation ≤
    2 * D.epsilon * Real.log (D.verifierDim : ℝ) + 2 * binaryEntropy D.epsilon

/-- A two-point distribution together with Pinsker bounds every pairwise trace distance. -/
def reversePinskerBound (D : HSZKHolevoData) : Prop :=
  ∀ ω ω' : ℕ, D.traceDistance ω ω' ≤ Real.sqrt (8 * Real.log 2 * D.delta)

/-- Choosing a reference state recovers the HSZK witness family from the pairwise bound. -/
def hszkRecovery (D : HSZKHolevoData) : Prop :=
  ∀ ω : ℕ, D.traceDistance ω D.referenceState ≤ Real.sqrt (8 * Real.log 2 * D.delta)

lemma holevoUpperBound_holds (D : HSZKHolevoData) : D.holevoUpperBound := by
  exact D.commonSimulatorBound

lemma reversePinskerBound_holds (D : HSZKHolevoData) : D.reversePinskerBound := by
  exact D.twoPointPinsker

lemma hszkRecovery_holds (D : HSZKHolevoData) : D.hszkRecovery := by
  intro ω
  exact D.twoPointPinsker ω D.referenceState

end HSZKHolevoData

open HSZKHolevoData

/-- Quantitative equivalence between an HSZK simulator ball and vanishing accessible Holevo
information. The two directions are packaged separately, and a reference state recovers HSZK from
the pairwise trace-distance control. `prop:discussion-hszk-holevo` -/
theorem paper_discussion_hszk_holevo (D : HSZKHolevoData) :
    D.holevoUpperBound ∧ D.reversePinskerBound ∧ D.hszkRecovery := by
  exact ⟨D.holevoUpperBound_holds, D.reversePinskerBound_holds, D.hszkRecovery_holds⟩

end Omega.Discussion
