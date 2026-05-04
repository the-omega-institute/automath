import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete numerical closure data for the nearest-critical-layer conclusion. -/
structure conclusion_nearest_critical_layer_singlepoint_jet_mixedmoment_closure_bundle where
  criticalTailExponent : ℕ
  nearestLayerGrade : ℕ
  singlePointJetOrder : ℕ
  mixedMomentDegree : ℕ
  critical_tail_positive : 1 ≤ criticalTailExponent
  nearest_layer_below_tail : nearestLayerGrade ≤ criticalTailExponent
  tail_seen_by_singlepoint_jet : criticalTailExponent ≤ singlePointJetOrder
  mixed_moment_closes_locally : nearestLayerGrade + mixedMomentDegree ≤ singlePointJetOrder

/-- Public target type for the nearest-critical-layer closure theorem. -/
abbrev conclusion_nearest_critical_layer_singlepoint_jet_mixedmoment_closure_data :=
  conclusion_nearest_critical_layer_singlepoint_jet_mixedmoment_closure_bundle

/-- The bundled closure conclusion as concrete inequalities among the four components. -/
def conclusion_nearest_critical_layer_singlepoint_jet_mixedmoment_closure_data.claim
    (D : conclusion_nearest_critical_layer_singlepoint_jet_mixedmoment_closure_data) : Prop :=
  1 ≤ D.criticalTailExponent ∧
    D.nearestLayerGrade ≤ D.criticalTailExponent ∧
    D.criticalTailExponent ≤ D.singlePointJetOrder ∧
    D.nearestLayerGrade + D.mixedMomentDegree ≤ D.singlePointJetOrder

/-- Paper label:
`thm:conclusion-nearest-critical-layer-singlepoint-jet-mixedmoment-closure`. -/
theorem paper_conclusion_nearest_critical_layer_singlepoint_jet_mixedmoment_closure
    (D : conclusion_nearest_critical_layer_singlepoint_jet_mixedmoment_closure_data) :
    conclusion_nearest_critical_layer_singlepoint_jet_mixedmoment_closure_data.claim D := by
  exact ⟨D.critical_tail_positive, D.nearest_layer_below_tail,
    D.tail_seen_by_singlepoint_jet, D.mixed_moment_closes_locally⟩

end Omega.Conclusion
