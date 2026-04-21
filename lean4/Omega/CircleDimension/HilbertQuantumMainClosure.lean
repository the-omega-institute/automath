import Omega.CircleDimension.BornPairing
import Omega.CircleDimension.CompositeHilbertCarrier
import Omega.CircleDimension.ContinuousSpectrumRepresentation
import Omega.CircleDimension.ContinuousUnitaryGroup
import Omega.CircleDimension.DiscreteUnitaryEvolution
import Omega.CircleDimension.Entanglement
import Omega.CircleDimension.QuantumChannels

namespace Omega.CircleDimension

open scoped BigOperators

/-- Concrete input package for the Hilbert/quantum closure summary. The fields are concrete
carrier, projection, Born, tensor-product, entanglement, discrete-evolution, and spectral-model
data already used by the imported wrappers. -/
structure HilbertQuantumMainClosureData where
  eventProjectionData : QuantumEventProjectionData
  bornPairingData : BornPairingData
  compositeHilbertData : CompositeHilbertCarrierData
  compositeIndependent :
    CompositeHilbertCarrierData.independentMechanisms compositeHilbertData
  entanglementData : EntanglementData
  entanglementWitness : EntanglementData.not_simple_tensor_ray entanglementData
  discreteUnitaryData : ReadableTimeWordUnitaryEvolutionData
  spectrumAlphabet : Type
  instFintypeSpectrumAlphabet : Fintype spectrumAlphabet

attribute [instance] HilbertQuantumMainClosureData.instFintypeSpectrumAlphabet

namespace HilbertQuantumMainClosureData

/-- Discrete Hilbert layer assembled from the already formalized Hilbert-carrier, event-projection,
Born, tensor-product, entanglement, discrete-evolution, and channel wrappers. -/
def discreteHilbertLayer (D : HilbertQuantumMainClosureData) : Prop :=
  D.eventProjectionData.toReadableTimeWordHilbertCarrierData.quotientTrueInnerProduct ∧
    D.eventProjectionData.toReadableTimeWordHilbertCarrierData.hilbertCompletionExists ∧
    D.eventProjectionData.eventProjectionExists ∧
    D.eventProjectionData.eventProjectionUnique ∧
    D.eventProjectionData.eventProjectionCovariant ∧
    (∀ e : D.bornPairingData.Event,
      0 ≤ D.bornPairingData.prob e ∧ D.bornPairingData.prob e ≤ 1) ∧
    (∀ F : Finset D.bornPairingData.Event,
      D.bornPairingData.pairwiseOrthogonal F →
        D.bornPairingData.complete F → (∑ e ∈ F, D.bornPairingData.prob e) = 1) ∧
    CompositeHilbertCarrierData.compositeCarrierIsTensorProduct D.compositeHilbertData ∧
    EntanglementData.entangled_ray D.entanglementData ∧
    D.discreteUnitaryData.descendsToQuotient ∧
    D.discreteUnitaryData.isometricQuotientShift ∧
    D.discreteUnitaryData.hasUnitaryExtension ∧
    unitaryVisibleRealization D.eventProjectionData.eventSubspace ∧
    foldChannelCompletelyPositive D.eventProjectionData.timeShift ∧
    foldChannelTracePreserving D.eventProjectionData.timeShift

/-- Continuous Schrödinger layer assembled from the continuous unitary-group and continuous-spectrum
wrappers. -/
def continuousSchrodingerLayer (D : HilbertQuantumMainClosureData) : Prop :=
  (∀ k, |cdimContinuousUnitaryPhase k| ≤ Real.pi) ∧
    (∀ s t k,
      cdimContinuousUnitaryFamily (s + t) k =
        cdimContinuousUnitaryFamily s k * cdimContinuousUnitaryFamily t k) ∧
    (∀ k, Continuous fun s => cdimContinuousUnitaryFamily s k) ∧
    (∀ k, cdimContinuousUnitaryFamily 0 k = 1) ∧
    (∀ k, cdimContinuousUnitaryFamily 1 k = cdimContinuousUnitarySpectrum k) ∧
    ContinuousSpectrumRepresentation (visibleVonNeumannAlgebra D.spectrumAlphabet)
      (sameTimeAddressProjection (A := D.spectrumAlphabet))

end HilbertQuantumMainClosureData

/-- Paper label: `thm:cdim-hilbert-quantum-main-closure`. -/
theorem paper_cdim_hilbert_quantum_main_closure (D : HilbertQuantumMainClosureData) :
    HilbertQuantumMainClosureData.discreteHilbertLayer D ∧
      HilbertQuantumMainClosureData.continuousSchrodingerLayer D := by
  have hHilbert :=
    paper_cdim_hilbert_carrier D.eventProjectionData.toReadableTimeWordHilbertCarrierData
  have hProj := paper_cdim_quantum_event_projections D.eventProjectionData
  have hBorn := paper_cdim_born_pairing D.bornPairingData
  have hTensor :=
    paper_cdim_composite_hilbert_carrier D.compositeHilbertData D.compositeIndependent
  have hEnt := paper_cdim_entanglement D.entanglementData D.entanglementWitness
  have hDiscrete := paper_cdim_discrete_unitary_evolution D.discreteUnitaryData
  have hChannel :=
    paper_cdim_quantum_channels D.eventProjectionData.shiftEvent D.eventProjectionData.eventSubspace
      D.eventProjectionData.timeShift D.eventProjectionData.eventSubspace_covariant
  have hSpectrum :=
    paper_circle_dimension_continuous_spectrum_representation D.spectrumAlphabet
  have hContinuous := paper_cdim_continuous_unitary_group
  rcases hHilbert with ⟨hTrue, hComplete⟩
  rcases hProj with ⟨hProjExists, hProjUnique, hProjCovariant⟩
  rcases hBorn with ⟨hBornBounds, hBornMass⟩
  rcases hDiscrete with ⟨hDescends, hIsometric, hUnitary⟩
  rcases hChannel with ⟨hVisible, hCP, hTP⟩
  rcases hContinuous with ⟨hPhase, hGroup, hCont, hZero, hOne⟩
  refine ⟨?_, ?_⟩
  · exact ⟨hTrue, hComplete, hProjExists, hProjUnique, hProjCovariant, hBornBounds, hBornMass,
      hTensor, hEnt, hDescends, hIsometric, hUnitary, hVisible, hCP, hTP⟩
  · exact ⟨hPhase, hGroup, hCont, hZero, hOne, hSpectrum⟩

end Omega.CircleDimension
