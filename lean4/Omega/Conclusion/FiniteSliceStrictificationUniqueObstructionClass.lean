import Omega.Conclusion.StrictificationBilayerMeasureAffineGauge
import Omega.POM.PwCountertermStrictificationCriterion

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-finite-slice-strictification-unique-obstruction-class`. -/
theorem paper_conclusion_finite_slice_strictification_unique_obstruction_class
    (D : conclusion_strictification_bilayer_measure_affine_gauge_data)
    (E : Omega.POM.pom_pw_counterterm_strictification_criterion_data) :
    D.conclusion_strictification_bilayer_measure_affine_gauge_measure_layer_unique ∧
      ((E.has_coboundary_solution ↔ E.has_strictifying_counterterm) ∧
        E.solution_space_is_affine) := by
  have hD := paper_conclusion_strictification_bilayer_measure_affine_gauge D
  have hE := Omega.POM.paper_pom_pw_counterterm_strictification_criterion E
  exact ⟨hD.1, hE⟩

end Omega.Conclusion
