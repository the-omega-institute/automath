import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.PhaseResidual

namespace Omega.TypedAddressBiaxialCompletion

/-- One local lift over a visible event, carrying its visible statistic and the local obstruction
class whose pushforward controls the visible residual. -/
structure LocalVisibleLift where
  visibleEvent : ℕ
  obstructionClass : ℤ
  visibleStatistic : ℚ

/-- Concrete two-lift package for the minimal interference pattern at one visible event. -/
structure MinimalInterferenceData where
  visibleEvent : ℕ
  leftLift : LocalVisibleLift
  rightLift : LocalVisibleLift
  left_projects : leftLift.visibleEvent = visibleEvent
  right_projects : rightLift.visibleEvent = visibleEvent

namespace MinimalInterferenceData

/-- Visible residual class of the left local lift. -/
def leftVisibleResidualClass (D : MinimalInterferenceData) : ℤ :=
  typedAddressPushforwardVisibleClass D.leftLift.obstructionClass

/-- Visible residual class of the right local lift. -/
def rightVisibleResidualClass (D : MinimalInterferenceData) : ℤ :=
  typedAddressPushforwardVisibleClass D.rightLift.obstructionClass

/-- Relative visible residual class between the two local lifts. -/
def relativeVisibleResidualClass (D : MinimalInterferenceData) : ℤ :=
  D.rightVisibleResidualClass - D.leftVisibleResidualClass

/-- Lowest-order interference term: it vanishes exactly when the relative visible residual class
is trivial, and otherwise records that residual class in the visible statistic. -/
def interferenceTerm (D : MinimalInterferenceData) : ℚ :=
  if D.relativeVisibleResidualClass = 0 then 0 else (D.relativeVisibleResidualClass : ℚ)

/-- Visible statistic obtained by summing the two local contributions and the interference
correction. -/
def visibleStatistic (D : MinimalInterferenceData) : ℚ :=
  D.leftLift.visibleStatistic + D.rightLift.visibleStatistic + D.interferenceTerm

/-- The visible statistic splits as a sum of the two local pieces plus the interference term. -/
def visibleStatisticSplitsWithInterference (D : MinimalInterferenceData) : Prop :=
  D.leftLift.visibleEvent = D.visibleEvent ∧
    D.rightLift.visibleEvent = D.visibleEvent ∧
    D.visibleStatistic =
      D.leftLift.visibleStatistic + D.rightLift.visibleStatistic + D.interferenceTerm

/-- A nontrivial visible residual class obstructs identically vanishing cross terms. -/
def nontrivialResidualClassForcesCrossTerm (D : MinimalInterferenceData) : Prop :=
  D.relativeVisibleResidualClass ≠ 0 → D.interferenceTerm ≠ 0

end MinimalInterferenceData

/-- Two local lifts over one visible event split the visible statistic into two local
contributions plus the lowest-order interference term, and a nontrivial relative visible residual
forces that cross term to persist.
    prop:typed-address-biaxial-completion-minimal-interference -/
theorem paper_typed_address_biaxial_completion_minimal_interference (D : MinimalInterferenceData) :
    D.visibleStatisticSplitsWithInterference ∧ D.nontrivialResidualClassForcesCrossTerm := by
  refine ⟨?_, ?_⟩
  · exact ⟨D.left_projects, D.right_projects, rfl⟩
  · intro hResidual
    simp [MinimalInterferenceData.interferenceTerm, hResidual]

end Omega.TypedAddressBiaxialCompletion
