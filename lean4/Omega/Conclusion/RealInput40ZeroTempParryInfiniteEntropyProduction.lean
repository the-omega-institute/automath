import Omega.Conclusion.Realinput40AnalyticRegularityEndpointTypeSeparation

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-realinput40-zero-temp-parry-infinite-entropy-production`. -/
theorem paper_conclusion_realinput40_zero_temp_parry_infinite_entropy_production :
    conclusion_realinput40_analytic_regularity_endpoint_type_separation_irreversible_parry ∧
      conclusion_realinput40_analytic_regularity_endpoint_type_separation_infinite_entropy_production := by
  exact
    ⟨conclusion_realinput40_analytic_regularity_endpoint_type_separation_parry_irreversible,
      conclusion_realinput40_analytic_regularity_endpoint_type_separation_entropy_unbounded⟩

end Omega.Conclusion
