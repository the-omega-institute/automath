import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.ComovingLayerPeeling

namespace Omega.CircleDimension

/-- Chapter-local wrapper for the recursive defect-measure layer-peeling argument. It mirrors the
typed-address comoving package while renaming the recovered stages to the CircleDimension-facing
formulation. -/
structure DefectMeasureRecursiveLayerPeelingData where
  residualFourierTransform : Prop
  decayGapEstimate : Prop
  layerInversion : Prop
  residualFourierTransform_h : residualFourierTransform
  decayGapEstimate_h : decayGapEstimate
  layerInversion_h : layerInversion
  leadingLayerRecovered : Prop
  currentLayerRecovered : Prop
  fullMeasureRecovered : Prop
  recoverLeadingLayer :
    residualFourierTransform → decayGapEstimate → leadingLayerRecovered
  recoverCurrentLayer :
    leadingLayerRecovered → layerInversion → currentLayerRecovered
  recoverMeasure : currentLayerRecovered → fullMeasureRecovered

/-- Convert the CircleDimension wrapper into the typed-address comoving layer-peeling package. -/
def DefectMeasureRecursiveLayerPeelingData.toComovingLayerPeelingData
    (D : DefectMeasureRecursiveLayerPeelingData) :
    Omega.TypedAddressBiaxialCompletion.ComovingLayerPeelingData where
  residualFourierTransform := D.residualFourierTransform
  leadingDecayGapEstimate := D.decayGapEstimate
  layerFourierInversion := D.layerInversion
  residualFourierTransform_h := D.residualFourierTransform_h
  leadingDecayGapEstimate_h := D.decayGapEstimate_h
  layerFourierInversion_h := D.layerInversion_h
  leadingDecayLayerIdentified := D.leadingLayerRecovered
  layerFourierRecovered := D.currentLayerRecovered
  fullMeasureRecovered := D.fullMeasureRecovered
  identifyLeadingLayer := D.recoverLeadingLayer
  recoverLayer := D.recoverCurrentLayer
  recoverMeasure := D.recoverMeasure

/-- Paper-facing recursive layer-peeling wrapper: after identifying the leading residual layer,
the current layer is inverted and finite recursion recovers the full defect measure.
    thm:cdim-defect-measure-recursive-layer-peeling -/
theorem paper_cdim_defect_measure_recursive_layer_peeling
    (D : DefectMeasureRecursiveLayerPeelingData) :
    D.leadingLayerRecovered ∧ D.currentLayerRecovered ∧ D.fullMeasureRecovered := by
  simpa [DefectMeasureRecursiveLayerPeelingData.toComovingLayerPeelingData] using
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_comoving_layer_peeling
      D.toComovingLayerPeelingData

end Omega.CircleDimension
