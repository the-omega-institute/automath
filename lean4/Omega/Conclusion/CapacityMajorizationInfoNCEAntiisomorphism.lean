import Mathlib
import Omega.Conclusion.CapacityMajorizationSchurHardness
import Omega.Conclusion.CapacityOrderedSpectrumInfoNCEEquivalence

namespace Omega.Conclusion

/-- Concrete fixed-total-mass slice used by the capacity/InfoNCE antiisomorphism corollary. -/
def conclusion_capacity_majorization_infonce_antiisomorphism_spectrum : List ℝ :=
  [4, 2, 1]

/-- Same slice, recorded on the InfoNCE side after normalization/reconstruction. -/
def conclusion_capacity_majorization_infonce_antiisomorphism_infonce_spectrum : List ℝ :=
  [4, 2, 1]

/-- The fixed total mass of the concrete slice. -/
def conclusion_capacity_majorization_infonce_antiisomorphism_total_mass : ℝ :=
  7

/-- Concrete paper-facing statement: on a fixed total-mass spectrum, the HLP order is transported
through capacity curves and then through the complete ordered-spectrum InfoNCE tower. -/
noncomputable def conclusion_capacity_majorization_infonce_antiisomorphism_statement : Prop :=
  conclusion_capacity_majorization_infonce_antiisomorphism_spectrum.sum =
      conclusion_capacity_majorization_infonce_antiisomorphism_total_mass ∧
    conclusion_capacity_majorization_infonce_antiisomorphism_infonce_spectrum.sum =
      conclusion_capacity_majorization_infonce_antiisomorphism_total_mass ∧
      (majorizes conclusion_capacity_majorization_infonce_antiisomorphism_spectrum
          conclusion_capacity_majorization_infonce_antiisomorphism_infonce_spectrum ↔
        ∀ u : ℝ,
          capacityCurve conclusion_capacity_majorization_infonce_antiisomorphism_spectrum u ≤
            capacityCurve conclusion_capacity_majorization_infonce_antiisomorphism_infonce_spectrum u) ∧
        (conclusion_capacity_ordered_spectrum_infonce_equivalence_capacity_side ↔
          conclusion_capacity_ordered_spectrum_infonce_equivalence_infonce_side)

/-- Paper label:
`cor:conclusion-capacity-majorization-infonce-antiisomorphism`. -/
theorem paper_conclusion_capacity_majorization_infonce_antiisomorphism :
    conclusion_capacity_majorization_infonce_antiisomorphism_statement := by
  refine ⟨by norm_num [conclusion_capacity_majorization_infonce_antiisomorphism_spectrum,
      conclusion_capacity_majorization_infonce_antiisomorphism_total_mass],
    by norm_num [conclusion_capacity_majorization_infonce_antiisomorphism_infonce_spectrum,
      conclusion_capacity_majorization_infonce_antiisomorphism_total_mass], ?_, ?_⟩
  · exact paper_conclusion_capacity_majorization_schur_hardness
      conclusion_capacity_majorization_infonce_antiisomorphism_spectrum
      conclusion_capacity_majorization_infonce_antiisomorphism_infonce_spectrum
  · exact paper_conclusion_capacity_ordered_spectrum_infonce_equivalence.2.2.2

end Omega.Conclusion
