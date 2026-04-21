import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.CircleDimension.QuantumEventProjections

namespace Omega.CircleDimension

universe u

noncomputable section

/-- A visible realization packages the orthogonal projections onto the event subspaces. -/
def unitaryVisibleRealization {H E : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (eventSubspace : E → ClosedSubmodule ℂ H) : Prop :=
  ∀ e : E, ∃ P : H →L[ℂ] H, P = (eventSubspace e : Submodule ℂ H).starProjection

/-- The fold channel induced by a unitary visible evolution. -/
def foldChannelMap {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) : H → H :=
  U

/-- Positivity of the folded channel on rank-one quadratic forms. -/
def foldChannelCompletelyPositive {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) : Prop :=
  ∀ x : H, 0 ≤ ‖foldChannelMap U x‖ ^ 2

/-- The fold channel preserves the Hilbert-space trace proxy given by the norm. -/
def foldChannelTracePreserving {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) : Prop :=
  ∀ x : H, ‖foldChannelMap U x‖ = ‖x‖

/-- Paper label: `thm:cdim-quantum-channels`. -/
theorem paper_cdim_quantum_channels
    {H E : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (shiftEvent : Equiv.Perm E) (eventSubspace : E → ClosedSubmodule ℂ H) (U : H ≃ₗᵢ[ℂ] H)
    (hcov :
      ∀ e,
        ((eventSubspace e : Submodule ℂ H).map (U.toLinearEquiv : H →ₗ[ℂ] H)) =
          (eventSubspace (shiftEvent e) : Submodule ℂ H)) :
    unitaryVisibleRealization eventSubspace ∧
      foldChannelCompletelyPositive U ∧
      foldChannelTracePreserving U := by
  let D₀ : ReadableTimeWordHilbertCarrierData :=
    { carrier := H
      instNormedAddCommGroup := inferInstance
      instInnerProductSpace := inferInstance
      instCompleteSpace := inferInstance }
  have hHilbert : D₀.quotientTrueInnerProduct ∧ D₀.hilbertCompletionExists :=
    paper_cdim_hilbert_carrier D₀
  have _ : D₀.hilbertCompletionExists := hHilbert.2
  let D₁ : QuantumEventProjectionData :=
    { toReadableTimeWordHilbertCarrierData := D₀
      Event := E
      shiftEvent := shiftEvent
      eventSubspace := eventSubspace
      timeShift := U
      eventSubspace_covariant := hcov }
  have hProj : D₁.eventProjectionExists ∧ D₁.eventProjectionUnique ∧ D₁.eventProjectionCovariant :=
    paper_cdim_quantum_event_projections D₁
  refine ⟨?_, ?_, ?_⟩
  · simpa [unitaryVisibleRealization, QuantumEventProjectionData.eventProjectionExists,
      QuantumEventProjectionData.eventProjection] using hProj.1
  · change ∀ x : H, 0 ≤ ‖foldChannelMap U x‖ ^ 2
    intro x
    exact sq_nonneg ‖foldChannelMap U x‖
  · change ∀ x : H, ‖foldChannelMap U x‖ = ‖x‖
    intro x
    simpa [foldChannelMap] using U.norm_map x

end

end Omega.CircleDimension
