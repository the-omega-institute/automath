import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Omega.CircleDimension.HilbertCarrier

namespace Omega.CircleDimension

universe u

/-- Concrete readable-time-word quantum-event data: a complex Hilbert carrier, a family of closed
event subspaces, and a unitary time-shift permuting those subspaces. -/
structure QuantumEventProjectionData extends ReadableTimeWordHilbertCarrierData where
  Event : Type u
  shiftEvent : Equiv.Perm Event
  eventSubspace : Event → ClosedSubmodule ℂ carrier
  timeShift : carrier ≃ₗᵢ[ℂ] carrier
  eventSubspace_covariant :
    ∀ e,
      ((eventSubspace e : Submodule ℂ carrier).map
          (timeShift.toLinearEquiv : carrier →ₗ[ℂ] carrier)) =
        (eventSubspace (shiftEvent e) : Submodule ℂ carrier)

instance (D : QuantumEventProjectionData) : NormedAddCommGroup D.carrier :=
  D.toReadableTimeWordHilbertCarrierData.instNormedAddCommGroup

instance (D : QuantumEventProjectionData) : InnerProductSpace ℂ D.carrier :=
  D.toReadableTimeWordHilbertCarrierData.instInnerProductSpace

instance (D : QuantumEventProjectionData) : CompleteSpace D.carrier :=
  D.toReadableTimeWordHilbertCarrierData.instCompleteSpace

noncomputable section

/-- The orthogonal projection onto the closed event subspace attached to `e`. -/
abbrev QuantumEventProjectionData.eventProjection
    (D : QuantumEventProjectionData) (e : D.Event) : D.carrier →L[ℂ] D.carrier :=
  (D.eventSubspace e : Submodule ℂ D.carrier).starProjection

/-- Every closed event subspace admits its canonical orthogonal projection. -/
def QuantumEventProjectionData.eventProjectionExists (D : QuantumEventProjectionData) : Prop :=
  ∀ e : D.Event, ∃ P : D.carrier →L[ℂ] D.carrier, P = D.eventProjection e

/-- The orthogonal projection is uniquely characterized by having values in the event subspace
and orthogonal residuals. -/
def QuantumEventProjectionData.eventProjectionUnique (D : QuantumEventProjectionData) : Prop :=
  ∀ e : D.Event, ∀ P : D.carrier →L[ℂ] D.carrier,
    (∀ x, P x ∈ (D.eventSubspace e : Submodule ℂ D.carrier)) →
      (∀ x, x - P x ∈ ((D.eventSubspace e : Submodule ℂ D.carrier)ᗮ)) →
        P = D.eventProjection e

/-- Conjugating by the unitary time shift carries each event projection to the projection onto the
shifted event subspace. -/
def QuantumEventProjectionData.eventProjectionCovariant (D : QuantumEventProjectionData) : Prop :=
  ∀ e : D.Event, ∀ x : D.carrier,
    D.timeShift (D.eventProjection e x) =
      D.eventProjection (D.shiftEvent e) (D.timeShift x)

/-- Paper label: `thm:cdim-quantum-event-projections`. -/
theorem paper_cdim_quantum_event_projections (D : QuantumEventProjectionData) :
    D.eventProjectionExists ∧ D.eventProjectionUnique ∧ D.eventProjectionCovariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    exact ⟨D.eventProjection e, rfl⟩
  · intro e P hMem hOrth
    ext x
    exact
      (Submodule.eq_starProjection_of_mem_orthogonal
        (K := (D.eventSubspace e : Submodule ℂ D.carrier)) (hMem x) (hOrth x)).symm
  · intro e x
    have hMap :=
      (Submodule.starProjection_map_apply D.timeShift
        (D.eventSubspace e : Submodule ℂ D.carrier) (D.timeShift x)).symm
    simpa [QuantumEventProjectionData.eventProjection, D.eventSubspace_covariant e] using hMap

end

end Omega.CircleDimension
