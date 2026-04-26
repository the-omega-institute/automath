import Omega.DerivedConsequences.DerivedM2Level3Common24Defect15ExactSequence
import Omega.DerivedConsequences.DerivedM2Level3Common24CrossboundaryStability

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-m2-level3-incidence-exact-sequence-15-separation`. -/
theorem paper_conclusion_m2_level3_incidence_exact_sequence_15_separation
    (D : Omega.DerivedConsequences.derived_m2_level3_common24_crossboundary_stability_data) :
    Omega.DerivedConsequences.derived_m2_level3_common24_defect15_exact_sequence_statement ∧
      Omega.DerivedConsequences.derived_m2_level3_common24_crossboundary_stability_first_v15_xi_charpoly ≠
        Omega.DerivedConsequences.derived_m2_level3_common24_crossboundary_stability_second_v15_xi_charpoly := by
  rcases Omega.DerivedConsequences.paper_derived_m2_level3_common24_crossboundary_stability D with
    ⟨hExact, _, _, _, _, hSep⟩
  exact ⟨hExact, hSep⟩

end Omega.Conclusion
