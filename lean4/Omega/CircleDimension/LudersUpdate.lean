import Omega.CircleDimension.BornPairing
import Omega.CircleDimension.QuantumEventProjections

namespace Omega.CircleDimension

noncomputable section

/-- The normalized post-measurement state attached to the event projection `Pₑ`. -/
def ludersUpdate {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (eventSubspace : E → ClosedSubmodule ℂ H) (prob : E → ℝ) (e : E) (ψ : H) : H :=
  ((prob e : ℂ)⁻¹) • ((eventSubspace e : Submodule ℂ H).starProjection ψ)

/-- Paper label: `cor:cdim-luders-update`. -/
theorem paper_cdim_luders_update
    {H E : Type} [Fintype E] [DecidableEq E] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (shiftEvent : Equiv.Perm E) (eventSubspace : E → ClosedSubmodule ℂ H)
    (U : H ≃ₗᵢ[ℂ] H)
    (hcov :
      ∀ e,
        ((eventSubspace e : Submodule ℂ H).map (U.toLinearEquiv : H →ₗ[ℂ] H)) =
          (eventSubspace (shiftEvent e) : Submodule ℂ H))
    (prob : E → ℝ) (hprob_nonneg : ∀ e, 0 ≤ prob e) (hprob_le_one : ∀ e, prob e ≤ 1)
    (htotal : (∑ e : E, prob e) = 1) :
    ∀ e : E, 0 < prob e →
      ∃ P : H →L[ℂ] H,
        P = (eventSubspace e : Submodule ℂ H).starProjection ∧
          (∀ ψ : H, ludersUpdate eventSubspace prob e ψ = ((prob e : ℂ)⁻¹) • P ψ) ∧
          (∀ ψ : H,
            U (P ψ) =
              ((eventSubspace (shiftEvent e) : Submodule ℂ H).starProjection) (U ψ)) ∧
          0 < prob e ∧ prob e ≤ 1 := by
  let D₀ : ReadableTimeWordHilbertCarrierData :=
    { carrier := H
      instNormedAddCommGroup := inferInstance
      instInnerProductSpace := inferInstance
      instCompleteSpace := inferInstance }
  let D₁ : QuantumEventProjectionData :=
    { toReadableTimeWordHilbertCarrierData := D₀
      Event := E
      shiftEvent := shiftEvent
      eventSubspace := eventSubspace
      timeShift := U
      eventSubspace_covariant := hcov }
  let B : BornPairingData :=
    { Event := E
      instFintype := inferInstance
      instDecidableEq := inferInstance
      prob := prob
      orthogonal := fun _ _ => True
      prob_nonneg := hprob_nonneg
      prob_le_one := hprob_le_one
      total_mass_univ := htotal }
  have hProj : D₁.eventProjectionExists ∧ D₁.eventProjectionUnique ∧ D₁.eventProjectionCovariant :=
    paper_cdim_quantum_event_projections D₁
  have hBorn :
      (∀ e : E, 0 ≤ B.prob e ∧ B.prob e ≤ 1) ∧
        (∀ F : Finset E, B.pairwiseOrthogonal F → B.complete F → (∑ e ∈ F, B.prob e) = 1) :=
    paper_cdim_born_pairing B
  intro e he
  obtain ⟨P, hP⟩ := hProj.1 e
  have hCov := hProj.2.2 e
  have hBounds := hBorn.1 e
  refine ⟨P, hP, ?_, ?_, ⟨he, hBounds.2⟩⟩
  · intro ψ
    rw [ludersUpdate, hP]
  · intro ψ
    simpa [hP, QuantumEventProjectionData.eventProjection] using hCov ψ

end

end Omega.CircleDimension
