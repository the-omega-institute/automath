import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

universe u

/-- Concrete carrier data for the readable-time-word Hilbert package. The quotient by the null
space is modeled by the carrier itself, corresponding to the definite quotient obtained after
dividing out the zero seminorm classes. -/
structure ReadableTimeWordHilbertCarrierData where
  carrier : Type u
  [instNormedAddCommGroup : NormedAddCommGroup carrier]
  [instInnerProductSpace : InnerProductSpace ℂ carrier]
  [instCompleteSpace : CompleteSpace carrier]

attribute [instance] ReadableTimeWordHilbertCarrierData.instNormedAddCommGroup
attribute [instance] ReadableTimeWordHilbertCarrierData.instInnerProductSpace
attribute [instance] ReadableTimeWordHilbertCarrierData.instCompleteSpace

/-- The definite quotient carrier. In this minimal formalization the null space has already been
modded out, so the quotient is represented by the carrier itself. -/
abbrev ReadableTimeWordHilbertCarrierData.quotientCarrier
    (D : ReadableTimeWordHilbertCarrierData) : Type u :=
  D.carrier

/-- The induced sesquilinear form on the quotient is definite. -/
def ReadableTimeWordHilbertCarrierData.quotientTrueInnerProduct
    (D : ReadableTimeWordHilbertCarrierData) : Prop :=
  ∀ x : D.quotientCarrier, ‖x‖ = 0 → x = 0

/-- A Hilbert completion exists for the quotient carrier. -/
def ReadableTimeWordHilbertCarrierData.hilbertCompletionExists
    (D : ReadableTimeWordHilbertCarrierData) : Prop :=
  CompleteSpace D.quotientCarrier

/-- Paper-facing wrapper for the readable-time-word Hilbert-carrier construction.
    thm:cdim-hilbert-carrier -/
theorem paper_cdim_hilbert_carrier (D : ReadableTimeWordHilbertCarrierData) :
    D.quotientTrueInnerProduct ∧ D.hilbertCompletionExists := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact norm_eq_zero.mp hx
  · change CompleteSpace D.quotientCarrier
    infer_instance

end Omega.CircleDimension
