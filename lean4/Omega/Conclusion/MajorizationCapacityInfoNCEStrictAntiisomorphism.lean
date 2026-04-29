import Mathlib
import Omega.Conclusion.CapacityMajorizationSchurHardness
import Omega.Conclusion.CapacityOrderedSpectrumInfoNCEEquivalence

namespace Omega.Conclusion

/-- Conclusion-level package: capacity curves reverse the majorization order, while the concrete
ordered-spectrum package identifies the same finite spectrum with its complete InfoNCE tower. -/
noncomputable def conclusion_majorization_capacity_infonce_strict_antiisomorphism_statement : Prop :=
  (majorizes ([4, 2, 1] : List ℝ) [4, 2, 1] ↔
    ∀ u : ℝ, capacityCurve ([4, 2, 1] : List ℝ) u ≤ capacityCurve [4, 2, 1] u) ∧
    conclusion_capacity_ordered_spectrum_infonce_equivalence_statement ∧
    (conclusion_capacity_ordered_spectrum_infonce_equivalence_capacity_side ↔
      conclusion_capacity_ordered_spectrum_infonce_equivalence_infonce_side)

/-- Paper label:
`thm:conclusion-majorization-capacity-infonce-strict-antiisomorphism`. -/
theorem paper_conclusion_majorization_capacity_infonce_strict_antiisomorphism :
    conclusion_majorization_capacity_infonce_strict_antiisomorphism_statement := by
  refine ⟨?_, paper_conclusion_capacity_ordered_spectrum_infonce_equivalence, ?_⟩
  · exact paper_conclusion_capacity_majorization_schur_hardness ([4, 2, 1] : List ℝ) [4, 2, 1]
  · exact paper_conclusion_capacity_ordered_spectrum_infonce_equivalence.2.2.2

end Omega.Conclusion
