import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local wrapper for the typed-address recursive layer-peeling argument.
It records the residual Fourier transform, the leading decay-gap estimate, and the per-layer
Fourier inversion step needed to peel one depth layer at a time and recover the full measure. -/
structure ComovingLayerPeelingData where
  residualFourierTransform : Prop
  leadingDecayGapEstimate : Prop
  layerFourierInversion : Prop
  residualFourierTransform_h : residualFourierTransform
  leadingDecayGapEstimate_h : leadingDecayGapEstimate
  layerFourierInversion_h : layerFourierInversion
  leadingDecayLayerIdentified : Prop
  layerFourierRecovered : Prop
  fullMeasureRecovered : Prop
  identifyLeadingLayer :
    residualFourierTransform → leadingDecayGapEstimate → leadingDecayLayerIdentified
  recoverLayer :
    leadingDecayLayerIdentified → layerFourierInversion → layerFourierRecovered
  recoverMeasure : layerFourierRecovered → fullMeasureRecovered

/-- Typed-address restatement of the recursive layer-peeling theorem: the residual Fourier
transform and its leading decay gap identify the current layer, Fourier inversion recovers that
layer, and finite recursion recovers the full measure.
    thm:typed-address-biaxial-completion-comoving-layer-peeling -/
theorem paper_typed_address_biaxial_completion_comoving_layer_peeling
    (D : ComovingLayerPeelingData) :
    D.leadingDecayLayerIdentified ∧ D.layerFourierRecovered ∧ D.fullMeasureRecovered := by
  have hLead : D.leadingDecayLayerIdentified :=
    D.identifyLeadingLayer D.residualFourierTransform_h D.leadingDecayGapEstimate_h
  have hLayer : D.layerFourierRecovered :=
    D.recoverLayer hLead D.layerFourierInversion_h
  exact ⟨hLead, hLayer, D.recoverMeasure hLayer⟩

end Omega.TypedAddressBiaxialCompletion
